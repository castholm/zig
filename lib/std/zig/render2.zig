const std = @import("../std.zig");
const assert = std.debug.assert;
const mem = std.mem;
const Allocator = std.mem.Allocator;
const meta = std.meta;
const Ast = std.zig.Ast;
const Token = std.zig.Token;
const primitives = std.zig.primitives;

const indent_delta = 4;
const asm_indent_delta = 2;

pub const Error = Ast.RenderError;

const Ais = AutoIndentingStream(std.ArrayList(u8).Writer);

pub const Fixups = struct {
    /// The key is the mut token (`var`/`const`) of the variable declaration
    /// that should have a `_ = foo;` inserted afterwards.
    unused_var_decls: std.AutoHashMapUnmanaged(Ast.TokenIndex, void) = .{},
    /// The functions in this unordered set of AST fn decl nodes will render
    /// with a function body of `@trap()` instead, with all parameters
    /// discarded.
    gut_functions: std.AutoHashMapUnmanaged(Ast.Node.Index, void) = .{},
    /// These global declarations will be omitted.
    omit_nodes: std.AutoHashMapUnmanaged(Ast.Node.Index, void) = .{},
    /// These expressions will be replaced with the string value.
    replace_nodes_with_string: std.AutoHashMapUnmanaged(Ast.Node.Index, []const u8) = .{},
    /// The string value will be inserted directly after the node.
    append_string_after_node: std.AutoHashMapUnmanaged(Ast.Node.Index, []const u8) = .{},
    /// These nodes will be replaced with a different node.
    replace_nodes_with_node: std.AutoHashMapUnmanaged(Ast.Node.Index, Ast.Node.Index) = .{},
    /// Change all identifier names matching the key to be value instead.
    rename_identifiers: std.StringArrayHashMapUnmanaged([]const u8) = .{},

    /// All `@import` builtin calls which refer to a file path will be prefixed
    /// with this path.
    rebase_imported_paths: ?[]const u8 = null,

    pub fn count(f: Fixups) usize {
        return f.unused_var_decls.count() +
            f.gut_functions.count() +
            f.omit_nodes.count() +
            f.replace_nodes_with_string.count() +
            f.append_string_after_node.count() +
            f.replace_nodes_with_node.count() +
            f.rename_identifiers.count() +
            @intFromBool(f.rebase_imported_paths != null);
    }

    pub fn clearRetainingCapacity(f: *Fixups) void {
        f.unused_var_decls.clearRetainingCapacity();
        f.gut_functions.clearRetainingCapacity();
        f.omit_nodes.clearRetainingCapacity();
        f.replace_nodes_with_string.clearRetainingCapacity();
        f.append_string_after_node.clearRetainingCapacity();
        f.replace_nodes_with_node.clearRetainingCapacity();
        f.rename_identifiers.clearRetainingCapacity();

        f.rebase_imported_paths = null;
    }

    pub fn deinit(f: *Fixups, gpa: Allocator) void {
        f.unused_var_decls.deinit(gpa);
        f.gut_functions.deinit(gpa);
        f.omit_nodes.deinit(gpa);
        f.replace_nodes_with_string.deinit(gpa);
        f.append_string_after_node.deinit(gpa);
        f.replace_nodes_with_node.deinit(gpa);
        f.rename_identifiers.deinit(gpa);
        f.* = undefined;
    }
};

const Render = struct {
    gpa: Allocator,
    ais: *Ais,
    tree: Ast,
    fixups: Fixups,
};

pub fn renderTree(buffer: *std.ArrayList(u8), tree: Ast, fixups: Fixups) Error!void {
    assert(tree.errors.len == 0); // Cannot render an invalid tree.
    var auto_indenting_stream: Ais = .{
        .indent_delta = indent_delta,
        .underlying_writer = buffer.writer(),
        .indent_stack = std.BitStack.init(buffer.allocator),
    };
    var r: Render = .{
        .gpa = buffer.allocator,
        .ais = &auto_indenting_stream,
        .tree = tree,
        .fixups = fixups,
    };

    // Render all the line comments at the beginning of the file.
    const comment_end_loc = tree.tokens.items(.start)[0];
    _ = try renderComments(&r, 0, comment_end_loc);

    if (tree.tokens.items(.tag)[0] == .container_doc_comment) {
        try renderContainerDocComments(&r, 0);
    }

    if (tree.mode == .zon) {
        try renderExpression(
            &r,
            tree.nodes.items(.data)[0].lhs,
            .newline,
        );
    } else {
        try renderMembers(&r, tree.rootDecls());
    }

    if (auto_indenting_stream.disabled_offset) |disabled_offset| {
        try writeFixingWhitespace(auto_indenting_stream.underlying_writer, tree.source[disabled_offset..]);
    }
}

/// Render all members in the given slice, keeping empty lines where appropriate
fn renderMembers(r: *Render, members: []const Ast.Node.Index) Error!void {
    const tree = r.tree;
    if (members.len == 0) return;
    const container: Container = for (members) |member| {
        if (tree.fullContainerField(member)) |field| if (!field.ast.tuple_like) break .other;
    } else .tuple;
    try renderMember(r, container, members[0], .newline);
    for (members[1..]) |member| {
        try renderExtraNewline(r, member);
        try renderMember(r, container, member, .newline);
    }
}

const Container = enum {
    @"enum",
    tuple,
    other,
};

fn renderMember(
    r: *Render,
    container: Container,
    decl: Ast.Node.Index,
    space: Space,
) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const node_tags = tree.nodes.items(.tag);
    const token_tags = tree.tokens.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    const datas = tree.nodes.items(.data);
    if (r.fixups.omit_nodes.contains(decl)) return;
    try renderDocComments(r, tree.firstToken(decl));
    switch (tree.nodes.items(.tag)[decl]) {
        .global_var_decl,
        .local_var_decl,
        .simple_var_decl,
        .aligned_var_decl,
        => return renderVarDecl(r, tree.fullVarDecl(decl).?, false, .semicolon),
        else => {},
    }
    _ = container;
    _ = space;
    _ = ais;
    _ = node_tags;
    _ = token_tags;
    _ = main_tokens;
    _ = datas;
}

fn renderExpression(r: *Render, node: Ast.Node.Index, space: Space) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const token_tags = tree.tokens.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    const node_tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (r.fixups.replace_nodes_with_string.get(node)) |replacement| {
        try ais.writer().writeAll(replacement);
        try renderOnlySpace(r, space);
        return;
    } else if (r.fixups.replace_nodes_with_node.get(node)) |replacement| {
        return renderExpression(r, replacement, space);
    }
    switch (node_tags[node]) {
        .identifier => {
            const token_index = main_tokens[node];
            return renderIdentifier(r, token_index, space, .preserve_when_shadowing);
        },

        .number_literal,
        .char_literal,
        .unreachable_literal,
        .anyframe_literal,
        .string_literal,
        => return renderToken(r, main_tokens[node], space),

        .block_two,
        .block_two_semicolon,
        => {
            const statements = [2]Ast.Node.Index{ datas[node].lhs, datas[node].rhs };
            if (datas[node].lhs == 0) {
                return renderBlock(r, node, statements[0..0], space);
            } else if (datas[node].rhs == 0) {
                return renderBlock(r, node, statements[0..1], space);
            } else {
                return renderBlock(r, node, statements[0..2], space);
            }
        },
        .block,
        .block_semicolon,
        => {
            const statements = tree.extra_data[datas[node].lhs..datas[node].rhs];
            return renderBlock(r, node, statements, space);
        },

        .add,
        .add_wrap,
        .add_sat,
        .array_cat,
        .array_mult,
        .assign,
        .assign_bit_and,
        .assign_bit_or,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_xor,
        .assign_div,
        .assign_sub,
        .assign_sub_wrap,
        .assign_sub_sat,
        .assign_mod,
        .assign_add,
        .assign_add_wrap,
        .assign_add_sat,
        .assign_mul,
        .assign_mul_wrap,
        .assign_mul_sat,
        .bang_equal,
        .bit_and,
        .bit_or,
        .shl,
        .shl_sat,
        .shr,
        .bit_xor,
        .bool_and,
        .bool_or,
        .div,
        .equal_equal,
        .greater_or_equal,
        .greater_than,
        .less_or_equal,
        .less_than,
        .merge_error_sets,
        .mod,
        .mul,
        .mul_wrap,
        .mul_sat,
        .sub,
        .sub_wrap,
        .sub_sat,
        .@"orelse",
        => {
            const infix = datas[node];
            try renderExpression(r, infix.lhs, .space);
            const op_token = main_tokens[node];
            if (tree.tokensOnSameLine(op_token, op_token + 1)) {
                try renderToken(r, op_token, .space);
            } else {
                ais.pushWeakIndent();
                try renderToken(r, op_token, .newline);
            }
            return renderExpression(r, infix.rhs, space);
        },

        .@"break" => {
            const main_token = main_tokens[node];
            const label_token = datas[node].lhs;
            const target = datas[node].rhs;
            if (label_token == 0 and target == 0) {
                try renderToken(r, main_token, space); // break keyword
            } else if (label_token == 0 and target != 0) {
                try renderToken(r, main_token, .space); // break keyword
                try renderExpression(r, target, space);
            } else if (label_token != 0 and target == 0) {
                try renderToken(r, main_token, .space); // break keyword
                try renderToken(r, label_token - 1, .none); // colon
                try renderIdentifier(r, label_token, space, .eagerly_unquote); // identifier
            } else if (label_token != 0 and target != 0) {
                try renderToken(r, main_token, .space); // break keyword
                try renderToken(r, label_token - 1, .none); // colon
                try renderIdentifier(r, label_token, .space, .eagerly_unquote); // identifier
                try renderExpression(r, target, space);
            }
        },

        .@"continue" => {
            const main_token = main_tokens[node];
            const label = datas[node].lhs;
            if (label != 0) {
                try renderToken(r, main_token, .space); // continue
                try renderToken(r, label - 1, .none); // :
                return renderIdentifier(r, label, space, .eagerly_unquote); // label
            } else {
                return renderToken(r, main_token, space); // continue
            }
        },

        .@"return" => {
            if (datas[node].lhs != 0) {
                try renderToken(r, main_tokens[node], .space);
                try renderExpression(r, datas[node].lhs, space);
            } else {
                try renderToken(r, main_tokens[node], space);
            }
        },

        .grouped_expression => {
            const lparen = main_tokens[node];
            const did_promote = try ais.promoteWeakIndent();
            if (!tree.tokensOnSameLine(lparen, lparen + 1)) ais.pushWeakIndent();
            try renderToken(r, lparen, .none); // lparen
            try renderExpression(r, datas[node].lhs, .none); // expr
            if (did_promote) ais.popIndent();
            try renderToken(r, datas[node].rhs, space); // rparen
        },

        .while_simple,
        .while_cont,
        .@"while",
        => return renderWhile(r, tree.fullWhile(node).?, space),

        .if_simple,
        .@"if",
        => return renderIf(r, tree.fullIf(node).?, space),

        .enum_literal => {
            try renderToken(r, main_tokens[node] - 1, .none); // .
            return renderIdentifier(r, main_tokens[node], space, .eagerly_unquote); // name
        },

        else => {},
    }
    _ = token_tags;
}

fn renderVarDecl(
    r: *Render,
    var_decl: Ast.full.VarDecl,
    /// Destructures intentionally ignore leading `comptime` tokens.
    ignore_comptime_token: bool,
    /// `comma_space` and `space` are used for destructure LHS decls.
    space: Space,
) Error!void {
    try renderVarDeclWithoutFixups(r, var_decl, ignore_comptime_token, space);
    if (r.fixups.unused_var_decls.contains(var_decl.ast.mut_token + 1)) {
        // Discard the variable like this: `_ = foo;`
        const w = r.ais.writer();
        try w.writeAll("_ = ");
        try w.writeAll(tokenSliceForRender(r.tree, var_decl.ast.mut_token + 1));
        try w.writeAll(";\n");
    }
}

fn renderVarDeclWithoutFixups(
    r: *Render,
    var_decl: Ast.full.VarDecl,
    /// Destructures intentionally ignore leading `comptime` tokens.
    ignore_comptime_token: bool,
    /// `comma_space` and `space` are used for destructure LHS decls.
    space: Space,
) Error!void {
    const tree = r.tree;
    const ais = r.ais;

    if (var_decl.visib_token) |visib_token| {
        try renderToken(r, visib_token, Space.space); // pub
    }

    if (var_decl.extern_export_token) |extern_export_token| {
        try renderToken(r, extern_export_token, Space.space); // extern

        if (var_decl.lib_name) |lib_name| {
            try renderToken(r, lib_name, Space.space); // "lib"
        }
    }

    if (var_decl.threadlocal_token) |thread_local_token| {
        try renderToken(r, thread_local_token, Space.space); // threadlocal
    }

    if (!ignore_comptime_token) {
        if (var_decl.comptime_token) |comptime_token| {
            try renderToken(r, comptime_token, Space.space); // comptime
        }
    }

    try renderToken(r, var_decl.ast.mut_token, .space); // var

    if (var_decl.ast.type_node != 0 or var_decl.ast.align_node != 0 or
        var_decl.ast.addrspace_node != 0 or var_decl.ast.section_node != 0 or
        var_decl.ast.init_node != 0)
    {
        const name_space = if (var_decl.ast.type_node == 0 and
            (var_decl.ast.align_node != 0 or
            var_decl.ast.addrspace_node != 0 or
            var_decl.ast.section_node != 0 or
            var_decl.ast.init_node != 0))
            Space.space
        else
            Space.none;

        try renderIdentifier(r, var_decl.ast.mut_token + 1, name_space, .preserve_when_shadowing); // name
    } else {
        return renderIdentifier(r, var_decl.ast.mut_token + 1, space, .preserve_when_shadowing); // name
    }

    if (var_decl.ast.type_node != 0) {
        try renderToken(r, var_decl.ast.mut_token + 2, Space.space); // :
        if (var_decl.ast.align_node != 0 or var_decl.ast.addrspace_node != 0 or
            var_decl.ast.section_node != 0 or var_decl.ast.init_node != 0)
        {
            try renderExpression(r, var_decl.ast.type_node, .space);
        } else {
            return renderExpression(r, var_decl.ast.type_node, space);
        }
    }

    if (var_decl.ast.align_node != 0) {
        const lparen = tree.firstToken(var_decl.ast.align_node) - 1;
        const align_kw = lparen - 1;
        const rparen = tree.lastToken(var_decl.ast.align_node) + 1;
        try renderToken(r, align_kw, Space.none); // align
        try renderToken(r, lparen, Space.none); // (
        try renderExpression(r, var_decl.ast.align_node, Space.none);
        if (var_decl.ast.addrspace_node != 0 or var_decl.ast.section_node != 0 or
            var_decl.ast.init_node != 0)
        {
            try renderToken(r, rparen, .space); // )
        } else {
            return renderToken(r, rparen, space); // )
        }
    }

    if (var_decl.ast.addrspace_node != 0) {
        const lparen = tree.firstToken(var_decl.ast.addrspace_node) - 1;
        const addrspace_kw = lparen - 1;
        const rparen = tree.lastToken(var_decl.ast.addrspace_node) + 1;
        try renderToken(r, addrspace_kw, Space.none); // addrspace
        try renderToken(r, lparen, Space.none); // (
        try renderExpression(r, var_decl.ast.addrspace_node, Space.none);
        if (var_decl.ast.section_node != 0 or var_decl.ast.init_node != 0) {
            try renderToken(r, rparen, .space); // )
        } else {
            try renderToken(r, rparen, .none); // )
            return renderToken(r, rparen + 1, Space.newline); // ;
        }
    }

    if (var_decl.ast.section_node != 0) {
        const lparen = tree.firstToken(var_decl.ast.section_node) - 1;
        const section_kw = lparen - 1;
        const rparen = tree.lastToken(var_decl.ast.section_node) + 1;
        try renderToken(r, section_kw, Space.none); // linksection
        try renderToken(r, lparen, Space.none); // (
        try renderExpression(r, var_decl.ast.section_node, Space.none);
        if (var_decl.ast.init_node != 0) {
            try renderToken(r, rparen, .space); // )
        } else {
            return renderToken(r, rparen, space); // )
        }
    }

    assert(var_decl.ast.init_node != 0);

    const eq_token = tree.firstToken(var_decl.ast.init_node) - 1;
    if (tree.tokensOnSameLine(eq_token, eq_token + 1)) {
        try renderToken(r, eq_token, .space); // =
    } else {
        ais.pushWeakIndent();
        try renderToken(r, eq_token, .newline); // =
    }
    return renderExpression(r, var_decl.ast.init_node, space); // ;
}

fn renderIf(r: *Render, if_node: Ast.full.If, space: Space) Error!void {
    return renderWhile(r, .{
        .ast = .{
            .while_token = if_node.ast.if_token,
            .cond_expr = if_node.ast.cond_expr,
            .cont_expr = 0,
            .then_expr = if_node.ast.then_expr,
            .else_expr = if_node.ast.else_expr,
        },
        .inline_token = null,
        .label_token = null,
        .payload_token = if_node.payload_token,
        .else_token = if_node.else_token,
        .error_token = if_node.error_token,
    }, space);
}

/// Note that this function is additionally used to render if expressions, with
/// respective values set to null.
fn renderWhile(r: *Render, while_node: Ast.full.While, space: Space) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const token_tags = tree.tokens.items(.tag);

    if (while_node.label_token) |label| {
        try renderIdentifier(r, label, .none, .eagerly_unquote); // label
        try renderToken(r, label + 1, .space); // :
    }

    if (while_node.inline_token) |inline_token| {
        try renderToken(r, inline_token, .space); // inline
    }

    try renderToken(r, while_node.ast.while_token, .space); // if/for/while
    var lparen = while_node.ast.while_token + 1;
    var did_promote = try ais.promoteWeakIndent();
    if (!tree.tokensOnSameLine(lparen, lparen + 1)) ais.pushWeakIndent();
    try renderToken(r, lparen, .none); // lparen
    try renderExpression(r, while_node.ast.cond_expr, .none); // condition
    if (did_promote) ais.popIndent();
    var last_prefix_token = tree.lastToken(while_node.ast.cond_expr) + 1; // rparen

    if (while_node.payload_token) |payload_token| {
        try renderToken(r, last_prefix_token, .space);
        try renderToken(r, payload_token - 1, .none); // |
        const ident = blk: {
            if (token_tags[payload_token] == .asterisk) {
                try renderToken(r, payload_token, .none); // *
                break :blk payload_token + 1;
            } else {
                break :blk payload_token;
            }
        };
        try renderIdentifier(r, ident, .none, .preserve_when_shadowing); // identifier
        const pipe = blk: {
            // ??? Is this a thing? Or is it an outdated language construct?
            if (token_tags[ident + 1] == .comma) {
                try renderToken(r, ident + 1, .space); // ,
                try renderIdentifier(r, ident + 2, .none, .preserve_when_shadowing); // index
                break :blk ident + 3;
            } else {
                break :blk ident + 1;
            }
        };
        last_prefix_token = pipe;
    }

    if (while_node.ast.cont_expr != 0) {
        try renderToken(r, last_prefix_token, .space);
        lparen = tree.firstToken(while_node.ast.cont_expr) - 1;
        try renderToken(r, lparen - 1, .space); // :
        did_promote = try ais.promoteWeakIndent();
        if (!tree.tokensOnSameLine(lparen, lparen + 1)) ais.pushWeakIndent();
        try renderToken(r, lparen, .none); // lparen
        try renderExpression(r, while_node.ast.cont_expr, .none); // expr
        if (did_promote) ais.popIndent();
        last_prefix_token = tree.lastToken(while_node.ast.cont_expr) + 1; // rparen
    }

    try renderThenElse(
        r,
        last_prefix_token,
        while_node.ast.then_expr,
        while_node.else_token,
        while_node.error_token,
        while_node.ast.else_expr,
        space,
    );
}

fn renderThenElse(
    r: *Render,
    last_prefix_token: Ast.TokenIndex,
    then_expr: Ast.Node.Index,
    else_token: Ast.TokenIndex,
    maybe_error_token: ?Ast.TokenIndex,
    else_expr: Ast.Node.Index,
    space: Space,
) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const node_tags = tree.nodes.items(.tag);
    const then_expr_is_block = nodeIsBlock(node_tags[then_expr]);
    var did_promote = try ais.promoteWeakIndent();
    const indent_then_expr =
        !then_expr_is_block and
        !tree.tokensOnSameLine(last_prefix_token, tree.firstToken(then_expr));
    if (indent_then_expr) {
        ais.pushWeakIndent();
        try renderToken(r, last_prefix_token, .newline);
    } else {
        try renderToken(r, last_prefix_token, .space);
    }

    if (else_expr != 0) {
        if (indent_then_expr) {
            try renderExpression(r, then_expr, .newline);
        } else {
            try renderExpression(r, then_expr, .space);
        }
        if (did_promote) ais.popIndent();

        var last_else_token = else_token;

        if (maybe_error_token) |error_token| {
            try renderToken(r, else_token, .space); // else
            try renderToken(r, error_token - 1, .none); // |
            try renderIdentifier(r, error_token, .none, .preserve_when_shadowing); // identifier
            last_else_token = error_token + 1; // |
        }

        did_promote = try ais.promoteWeakIndent();
        const indent_else_expr =
            indent_then_expr and
            !nodeIsBlock(node_tags[else_expr]) and
            !nodeIsIfForWhileSwitch(node_tags[else_expr]);
        if (indent_else_expr) {
            ais.pushWeakIndent();
            try renderToken(r, last_else_token, .newline);
            try renderExpressionIndented(r, else_expr, space);
        } else {
            try renderToken(r, last_else_token, .space);
            try renderExpression(r, else_expr, space);
        }
    } else {
        if (indent_then_expr) {
            try renderExpressionIndented(r, then_expr, space);
        } else {
            try renderExpression(r, then_expr, space);
        }
    }
    if (did_promote) ais.popIndent();
}

fn renderBlock(
    r: *Render,
    block_node: Ast.Node.Index,
    statements: []const Ast.Node.Index,
    space: Space,
) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const token_tags = tree.tokens.items(.tag);
    const lbrace = tree.nodes.items(.main_token)[block_node];

    if (token_tags[lbrace - 1] == .colon and
        token_tags[lbrace - 2] == .identifier)
    {
        try renderIdentifier(r, lbrace - 2, .none, .eagerly_unquote); // identifier
        try renderToken(r, lbrace - 1, .space); // :
    }
    if (statements.len == 0) {
        try renderToken(r, lbrace, .none);
        try renderToken(r, tree.lastToken(block_node), space); // rbrace
        return;
    }
    try ais.pushIndent();
    try renderToken(r, lbrace, .newline);
    return finishRenderBlock(r, block_node, statements, space);
}

fn finishRenderBlock(
    r: *Render,
    block_node: Ast.Node.Index,
    statements: []const Ast.Node.Index,
    space: Space,
) Error!void {
    const tree = r.tree;
    const node_tags = tree.nodes.items(.tag);
    const ais = r.ais;
    for (statements, 0..) |stmt, i| {
        if (i != 0) try renderExtraNewline(r, stmt);
        if (r.fixups.omit_nodes.contains(stmt)) continue;
        switch (node_tags[stmt]) {
            .global_var_decl,
            .local_var_decl,
            .simple_var_decl,
            .aligned_var_decl,
            => try renderVarDecl(r, tree.fullVarDecl(stmt).?, false, .semicolon),

            else => try renderExpression(r, stmt, .semicolon),
        }
    }
    ais.popIndent();

    try renderToken(r, tree.lastToken(block_node), space); // rbrace
}

/// Renders the given expression indented, popping the indent before rendering
/// any following line comments
fn renderExpressionIndented(r: *Render, node: Ast.Node.Index, space: Space) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const token_starts = tree.tokens.items(.start);
    const token_tags = tree.tokens.items(.tag);

    try ais.pushIndent();

    var last_token = tree.lastToken(node);
    const punctuation = switch (space) {
        .none, .space, .newline, .skip => false,
        .comma => true,
        .comma_space => token_tags[last_token + 1] == .comma,
        .semicolon => token_tags[last_token + 1] == .semicolon,
    };

    try renderExpression(r, node, if (punctuation) .none else .skip);

    switch (space) {
        .none, .space, .newline, .skip => {},
        .comma => {
            if (token_tags[last_token + 1] == .comma) {
                try renderToken(r, last_token + 1, .skip);
                last_token += 1;
            } else {
                try ais.writer().writeByte(',');
            }
        },
        .comma_space => if (token_tags[last_token + 1] == .comma) {
            try renderToken(r, last_token + 1, .skip);
            last_token += 1;
        },
        .semicolon => if (token_tags[last_token + 1] == .semicolon) {
            try renderToken(r, last_token + 1, .skip);
            last_token += 1;
        },
    }

    ais.popIndent();

    if (space == .skip) return;

    const comment_start = token_starts[last_token] + tokenSliceForRender(tree, last_token).len;
    const comment = try renderComments(r, comment_start, token_starts[last_token + 1]);

    if (!comment) switch (space) {
        .none => {},
        .space,
        .comma_space,
        => try ais.writer().writeByte(' '),
        .newline,
        .comma,
        .semicolon,
        => try ais.writer().writeByte('\n'),
        .skip => unreachable,
    };
}

const Space = enum {
    /// Output the token lexeme only.
    none,
    /// Output the token lexeme followed by a single space.
    space,
    /// Output the token lexeme followed by a newline.
    newline,
    /// If the next token is a comma, render it as well. If not, insert one.
    /// In either case, a newline will be inserted afterwards.
    comma,
    /// Additionally consume the next token if it is a comma.
    /// In either case, a space will be inserted afterwards.
    comma_space,
    /// Additionally consume the next token if it is a semicolon.
    /// In either case, a newline will be inserted afterwards.
    semicolon,
    /// Skip rendering whitespace and comments. If this is used, the caller
    /// *must* handle whitespace and comments manually.
    skip,
};

fn renderToken(r: *Render, token_index: Ast.TokenIndex, space: Space) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const lexeme = tokenSliceForRender(tree, token_index);
    try ais.writer().writeAll(lexeme);
    try renderSpace(r, token_index, lexeme.len, space);
}

fn renderSpace(r: *Render, token_index: Ast.TokenIndex, lexeme_len: usize, space: Space) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const token_tags = tree.tokens.items(.tag);
    const token_starts = tree.tokens.items(.start);

    const token_start = token_starts[token_index];

    if (space == .skip) return;

    if (space == .comma and token_tags[token_index + 1] != .comma) {
        try ais.writer().writeByte(',');
    }

    const comment = try renderComments(r, token_start + lexeme_len, token_starts[token_index + 1]);

    if (space == .comma or space == .semicolon) {
        ais.popWeakIndent();
    }

    switch (space) {
        .none => {},
        .space => if (!comment) try ais.writer().writeByte(' '),
        .newline => if (!comment) try ais.writer().writeByte('\n'),

        .comma => if (token_tags[token_index + 1] == .comma) {
            try renderToken(r, token_index + 1, .newline);
        } else if (!comment) {
            try ais.writer().writeByte('\n');
        },

        .comma_space => if (token_tags[token_index + 1] == .comma) {
            try renderToken(r, token_index + 1, .space);
        } else if (!comment) {
            try ais.writer().writeByte(' ');
        },

        .semicolon => if (token_tags[token_index + 1] == .semicolon) {
            try renderToken(r, token_index + 1, .newline);
        } else if (!comment) {
            try ais.writer().writeByte('\n');
        },

        .skip => unreachable,
    }
}

fn renderOnlySpace(r: *Render, space: Space) Error!void {
    const ais = r.ais;
    switch (space) {
        .none => {},
        .space => try ais.writer().writeByte(' '),
        .newline => try ais.writer().writeByte('\n'),
        .comma => try ais.writer().writeAll(",\n"),
        .comma_space => try ais.writer().writeAll(", "),
        .semicolon => try ais.writer().writeAll(";\n"),
        .skip => unreachable,
    }
}

const QuoteBehavior = enum {
    preserve_when_shadowing,
    eagerly_unquote,
    eagerly_unquote_except_underscore,
};

fn renderIdentifier(r: *Render, token_index: Ast.TokenIndex, space: Space, quote: QuoteBehavior) Error!void {
    const tree = r.tree;
    const token_tags = tree.tokens.items(.tag);
    assert(token_tags[token_index] == .identifier);
    const lexeme = tokenSliceForRender(tree, token_index);

    if (r.fixups.rename_identifiers.get(lexeme)) |mangled| {
        try r.ais.writer().writeAll(mangled);
        try renderSpace(r, token_index, lexeme.len, space);
        return;
    }

    if (lexeme[0] != '@') {
        return renderToken(r, token_index, space);
    }

    assert(lexeme.len >= 3);
    assert(lexeme[0] == '@');
    assert(lexeme[1] == '\"');
    assert(lexeme[lexeme.len - 1] == '\"');
    const contents = lexeme[2 .. lexeme.len - 1]; // inside the @"" quotation

    // Empty name can't be unquoted.
    if (contents.len == 0) {
        return renderQuotedIdentifier(r, token_index, space, false);
    }

    // Special case for _ which would incorrectly be rejected by isValidId below.
    if (contents.len == 1 and contents[0] == '_') switch (quote) {
        .eagerly_unquote => return renderQuotedIdentifier(r, token_index, space, true),
        .eagerly_unquote_except_underscore,
        .preserve_when_shadowing,
        => return renderQuotedIdentifier(r, token_index, space, false),
    };

    // Scan the entire name for characters that would (after un-escaping) be illegal in a symbol,
    // i.e. contents don't match: [A-Za-z_][A-Za-z0-9_]*
    var contents_i: usize = 0;
    while (contents_i < contents.len) {
        switch (contents[contents_i]) {
            '0'...'9' => if (contents_i == 0) return renderQuotedIdentifier(r, token_index, space, false),
            'A'...'Z', 'a'...'z', '_' => {},
            '\\' => {
                var esc_offset = contents_i;
                const res = std.zig.string_literal.parseEscapeSequence(contents, &esc_offset);
                switch (res) {
                    .success => |char| switch (char) {
                        '0'...'9' => if (contents_i == 0) return renderQuotedIdentifier(r, token_index, space, false),
                        'A'...'Z', 'a'...'z', '_' => {},
                        else => return renderQuotedIdentifier(r, token_index, space, false),
                    },
                    .failure => return renderQuotedIdentifier(r, token_index, space, false),
                }
                contents_i += esc_offset;
                continue;
            },
            else => return renderQuotedIdentifier(r, token_index, space, false),
        }
        contents_i += 1;
    }

    // Read enough of the name (while un-escaping) to determine if it's a keyword or primitive.
    // If it's too long to fit in this buffer, we know it's neither and quoting is unnecessary.
    // If we read the whole thing, we have to do further checks.
    const longest_keyword_or_primitive_len = comptime blk: {
        var longest = 0;
        for (primitives.names.kvs) |kv| {
            if (kv.key.len > longest) longest = kv.key.len;
        }
        for (std.zig.Token.keywords.kvs) |kv| {
            if (kv.key.len > longest) longest = kv.key.len;
        }
        break :blk longest;
    };
    var buf: [longest_keyword_or_primitive_len]u8 = undefined;

    contents_i = 0;
    var buf_i: usize = 0;
    while (contents_i < contents.len and buf_i < longest_keyword_or_primitive_len) {
        if (contents[contents_i] == '\\') {
            const res = std.zig.string_literal.parseEscapeSequence(contents, &contents_i).success;
            buf[buf_i] = @as(u8, @intCast(res));
            buf_i += 1;
        } else {
            buf[buf_i] = contents[contents_i];
            contents_i += 1;
            buf_i += 1;
        }
    }

    // We read the whole thing, so it could be a keyword or primitive.
    if (contents_i == contents.len) {
        if (!std.zig.isValidId(buf[0..buf_i])) {
            return renderQuotedIdentifier(r, token_index, space, false);
        }
        if (primitives.isPrimitive(buf[0..buf_i])) switch (quote) {
            .eagerly_unquote,
            .eagerly_unquote_except_underscore,
            => return renderQuotedIdentifier(r, token_index, space, true),
            .preserve_when_shadowing => return renderQuotedIdentifier(r, token_index, space, false),
        };
    }

    try renderQuotedIdentifier(r, token_index, space, true);
}

// Renders a @"" quoted identifier, normalizing escapes.
// Unnecessary escapes are un-escaped, and \u escapes are normalized to \x when they fit.
// If unquote is true, the @"" is removed and the result is a bare symbol whose validity is asserted.
fn renderQuotedIdentifier(r: *Render, token_index: Ast.TokenIndex, space: Space, comptime unquote: bool) !void {
    const tree = r.tree;
    const ais = r.ais;
    const token_tags = tree.tokens.items(.tag);
    assert(token_tags[token_index] == .identifier);
    const lexeme = tokenSliceForRender(tree, token_index);
    assert(lexeme.len >= 3 and lexeme[0] == '@');

    if (!unquote) try ais.writer().writeAll("@\"");
    const contents = lexeme[2 .. lexeme.len - 1];
    try renderIdentifierContents(ais.writer(), contents);
    if (!unquote) try ais.writer().writeByte('\"');

    try renderSpace(r, token_index, lexeme.len, space);
}

fn renderIdentifierContents(writer: anytype, bytes: []const u8) !void {
    var pos: usize = 0;
    while (pos < bytes.len) {
        const byte = bytes[pos];
        switch (byte) {
            '\\' => {
                const old_pos = pos;
                const res = std.zig.string_literal.parseEscapeSequence(bytes, &pos);
                const escape_sequence = bytes[old_pos..pos];
                switch (res) {
                    .success => |codepoint| {
                        if (codepoint <= 0x7f) {
                            const buf = [1]u8{@as(u8, @intCast(codepoint))};
                            try std.fmt.format(writer, "{}", .{std.zig.fmtEscapes(&buf)});
                        } else {
                            try writer.writeAll(escape_sequence);
                        }
                    },
                    .failure => {
                        try writer.writeAll(escape_sequence);
                    },
                }
            },
            0x00...('\\' - 1), ('\\' + 1)...0x7f => {
                const buf = [1]u8{byte};
                try std.fmt.format(writer, "{}", .{std.zig.fmtEscapes(&buf)});
                pos += 1;
            },
            0x80...0xff => {
                try writer.writeByte(byte);
                pos += 1;
            },
        }
    }
}

/// Assumes that start is the first byte past the previous token and
/// that end is the last byte before the next token.
fn renderComments(r: *Render, start: usize, end: usize) Error!bool {
    const tree = r.tree;
    const ais = r.ais;

    var index: usize = start;
    while (mem.indexOf(u8, tree.source[index..end], "//")) |offset| {
        const comment_start = index + offset;

        // If there is no newline, the comment ends with EOF
        const newline_index = mem.indexOfScalar(u8, tree.source[comment_start..end], '\n');
        const newline = if (newline_index) |i| comment_start + i else null;

        const untrimmed_comment = tree.source[comment_start .. newline orelse tree.source.len];
        const trimmed_comment = mem.trimRight(u8, untrimmed_comment, &std.ascii.whitespace);

        // Don't leave any whitespace at the start of the file
        if (index != 0) {
            if (index == start and mem.containsAtLeast(u8, tree.source[index..comment_start], 2, "\n")) {
                // Leave up to one empty line before the first comment
                try ais.writer().writeByte('\n');
                try ais.writer().writeByte('\n');
            } else if (mem.indexOfScalar(u8, tree.source[index..comment_start], '\n') != null) {
                // Respect the newline directly before the comment.
                // Note: This allows an empty line between comments
                try ais.writer().writeByte('\n');
            } else if (index == start) {
                // Otherwise if the first comment is on the same line as
                // the token before it, prefix it with a single space.
                try ais.writer().writeByte(' ');
            }
        }

        index = 1 + (newline orelse end - 1);

        const comment_content = mem.trimLeft(u8, trimmed_comment["//".len..], &std.ascii.whitespace);
        if (ais.disabled_offset != null and mem.eql(u8, comment_content, "zig fmt: on")) {
            // Write the source for which formatting was disabled directly
            // to the underlying writer, fixing up invalid whitespace.
            const disabled_source = tree.source[ais.disabled_offset.?..comment_start];
            try writeFixingWhitespace(ais.underlying_writer, disabled_source);
            // Write with the canonical single space.
            try ais.underlying_writer.writeAll("// zig fmt: on\n");
            ais.disabled_offset = null;
        } else if (ais.disabled_offset == null and mem.eql(u8, comment_content, "zig fmt: off")) {
            // Write with the canonical single space.
            try ais.writer().writeAll("// zig fmt: off\n");
            ais.disabled_offset = index;
        } else {
            // Write the comment minus trailing whitespace.
            try ais.writer().print("{s}\n", .{trimmed_comment});
        }
    }

    if (index != start and mem.containsAtLeast(u8, tree.source[index - 1 .. end], 2, "\n")) {
        // Don't leave any whitespace at the end of the file
        if (end != tree.source.len) {
            try ais.writer().writeByte('\n');
        }
    }

    return index != start;
}

fn renderExtraNewline(r: *Render, node: Ast.Node.Index) Error!void {
    return renderExtraNewlineToken(r, r.tree.firstToken(node));
}

/// Check if there is an empty line immediately before the given token. If so, render it.
fn renderExtraNewlineToken(r: *Render, token_index: Ast.TokenIndex) Error!void {
    const tree = r.tree;
    const ais = r.ais;
    const token_starts = tree.tokens.items(.start);
    const token_start = token_starts[token_index];
    if (token_start == 0) return;
    const prev_token_end = if (token_index == 0)
        0
    else
        token_starts[token_index - 1] + tokenSliceForRender(tree, token_index - 1).len;

    // If there is a immediately preceding comment or doc_comment,
    // skip it because required extra newline has already been rendered.
    if (mem.indexOf(u8, tree.source[prev_token_end..token_start], "//") != null) return;
    if (token_index > 0 and tree.tokens.items(.tag)[token_index - 1] == .doc_comment) return;

    // Iterate backwards to the end of the previous token, stopping if a
    // non-whitespace character is encountered or two newlines have been found.
    var i = token_start - 1;
    var newlines: u2 = 0;
    while (std.ascii.isWhitespace(tree.source[i])) : (i -= 1) {
        if (tree.source[i] == '\n') newlines += 1;
        if (newlines == 2) return ais.writer().writeByte('\n');
        if (i == prev_token_end) break;
    }
}

/// end_token is the token one past the last doc comment token. This function
/// searches backwards from there.
fn renderDocComments(r: *Render, end_token: Ast.TokenIndex) Error!void {
    const tree = r.tree;
    // Search backwards for the first doc comment.
    const token_tags = tree.tokens.items(.tag);
    if (end_token == 0) return;
    var tok = end_token - 1;
    while (token_tags[tok] == .doc_comment) {
        if (tok == 0) break;
        tok -= 1;
    } else {
        tok += 1;
    }
    const first_tok = tok;
    if (first_tok == end_token) return;

    if (first_tok != 0) {
        const prev_token_tag = token_tags[first_tok - 1];

        // Prevent accidental use of `renderDocComments` for a function argument doc comment
        assert(prev_token_tag != .l_paren);

        if (prev_token_tag != .l_brace) {
            try renderExtraNewlineToken(r, first_tok);
        }
    }

    while (token_tags[tok] == .doc_comment) : (tok += 1) {
        try renderToken(r, tok, .newline);
    }
}

/// start_token is first container doc comment token.
fn renderContainerDocComments(r: *Render, start_token: Ast.TokenIndex) Error!void {
    const tree = r.tree;
    const token_tags = tree.tokens.items(.tag);
    var tok = start_token;
    while (token_tags[tok] == .container_doc_comment) : (tok += 1) {
        try renderToken(r, tok, .newline);
    }
    // Render extra newline if there is one between final container doc comment and
    // the next token. If the next token is a doc comment, that code path
    // will have its own logic to insert a newline.
    if (token_tags[tok] != .doc_comment) {
        try renderExtraNewlineToken(r, tok);
    }
}

fn tokenSliceForRender(tree: Ast, token_index: Ast.TokenIndex) []const u8 {
    var ret = tree.tokenSlice(token_index);
    switch (tree.tokens.items(.tag)[token_index]) {
        .multiline_string_literal_line => {
            if (ret[ret.len - 1] == '\n') ret.len -= 1;
        },
        .container_doc_comment, .doc_comment => {
            ret = mem.trimRight(u8, ret, &std.ascii.whitespace);
        },
        else => {},
    }
    return ret;
}

fn writeFixingWhitespace(writer: std.ArrayList(u8).Writer, slice: []const u8) Error!void {
    for (slice) |byte| switch (byte) {
        '\t' => try writer.writeAll(" " ** 4),
        '\r' => {},
        else => try writer.writeByte(byte),
    };
}

fn nodeIsBlock(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        => true,
        else => false,
    };
}

fn nodeIsIfForWhileSwitch(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .@"if",
        .if_simple,
        .@"for",
        .for_simple,
        .@"while",
        .while_simple,
        .while_cont,
        .@"switch",
        .switch_comma,
        => true,
        else => false,
    };
}

/// Automatically inserts indentation of written data by keeping
/// track of the current indentation level
fn AutoIndentingStream(comptime UnderlyingWriter: type) type {
    return struct {
        const Self = @This();
        pub const WriteError = UnderlyingWriter.Error;
        pub const Writer = std.io.Writer(*Self, WriteError, write);

        underlying_writer: UnderlyingWriter,

        /// Offset into the source at which formatting has been disabled with
        /// a `zig fmt: off` comment.
        ///
        /// If non-null, the AutoIndentingStream will not write any bytes
        /// to the underlying writer. It will however continue to track the
        /// indentation level.
        disabled_offset: ?usize = null,

        indent_stack: std.BitStack, // Element: weak_indent
        indent_delta: usize,
        current_line_empty: bool = true,
        weak_indent: u1 = 0,

        pub fn writer(self: *Self) Writer {
            return .{ .context = self };
        }

        pub fn write(self: *Self, bytes: []const u8) WriteError!usize {
            if (bytes.len == 0) return 0;

            const current_indent = (self.indent_stack.bit_len + self.weak_indent) * self.indent_delta;
            if (self.disabled_offset == null) {
                if (self.current_line_empty and !(bytes.len == 1 and bytes[0] == '\n')) {
                    try self.underlying_writer.writeByteNTimes(' ', current_indent);
                }
                try self.underlying_writer.writeAll(bytes);
            }
            self.current_line_empty = bytes[bytes.len - 1] == '\n';

            return bytes.len;
        }

        pub fn pushIndent(self: *Self) Allocator.Error!void {
            try self.indent_stack.push(self.weak_indent);
            self.weak_indent = 0;
        }

        pub fn pushWeakIndent(self: *Self) void {
            self.weak_indent +|= 1;
        }

        pub fn promoteWeakIndent(self: *Self) Allocator.Error!bool {
            if (self.weak_indent != 0) {
                try self.pushIndent();
                return true;
            } else {
                return false;
            }
        }

        pub fn popIndent(self: *Self) void {
            assert(self.indent_delta != 0);
            self.weak_indent = self.indent_stack.pop();
        }

        pub fn popWeakIndent(self: *Self) void {
            self.weak_indent -|= 1;
        }
    };
}
