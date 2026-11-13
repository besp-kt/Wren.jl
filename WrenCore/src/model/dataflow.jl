# A crude, syntax-level, dataflow analysis for Sample statements in Wren model bodies.

using Accessors: Accessors

get_used_symbols(::Any) = Set{Symbol}() # literals etc
get_used_symbols(::QuoteNode) = Set{Symbol}()
get_used_symbols(symbol::Symbol) = Set([symbol])
function get_used_symbols(expr::Union{Expr,WrenExpr})
    # Skip names of keyword arguments and names of macros
    args_to_check = if expr.head === :kw || expr.head === :macrocall
        expr.args[2:end]
    else
        expr.args
    end
    return union(Set{Symbol}(), get_used_symbols.(args_to_check)...)
end
get_used_symbols(stmt::OtherStatement) = get_used_symbols(stmt.expr)
function get_used_symbols(::AbstractWrenExpr)
    _issue_error("unhandled node in get_used_symbols")
end

get_lhs_index_symbols(::Symbol) = Set{Symbol}()
function get_lhs_index_symbols(expr::Expr)
    return if Meta.isexpr(expr, :ref)
        union(get_lhs_index_symbols(expr.args[1]), get_used_symbols.(expr.args[2:end])...)
    elseif Meta.isexpr(expr, :.)
        get_lhs_index_symbols(expr.args[1])
    else
        get_used_symbols(expr)
    end
end

struct DataflowAnalysisState
    # All top-level symbols on the LHS of Sample nodes, and names of GeneratedQuantity nodes
    lhs_syms::Set{Symbol}
    # Top-level symbols on the LHS of Sample nodes
    sample_syms::Set{Symbol}
    # Names of GeneratedQuantity nodes
    gq_syms::Set{Symbol}
    # The subset of `lhs_syms` that were seen again in a later expression, which we thus
    # need the values of
    required_syms::Set{Symbol}
    # Generated quantities that are not required, i.e. whose expressions are only
    # evaluated when a generated quantity that depends on them is requested. This is
    # filled in by `analyse_dataflow` after the traversal.
    skippable_gqs::Set{Symbol}
    # For each generated quantity, the `lhs_syms` used in its expression. Uses inside
    # generated quantity expressions are recorded here instead of `required_syms`, because
    # whether they are required depends on whether the generated quantity is required.
    gq_uses::Dict{Symbol,Set{Symbol}}
    # The generated quantity whose expression is being traversed, if any
    enclosing_gq::Base.RefValue{Union{Nothing,Symbol}}
    # All model arguments
    args::Set{Symbol}
    # Arguments which have potentially been written to
    dirty_args::Set{Symbol}
    # Dirty arguments which have potentially been read from again
    args_to_copy::Set{Symbol}
end
function DataflowAnalysisState(args::Set{Symbol})
    return DataflowAnalysisState(
        Set{Symbol}(),
        Set{Symbol}(),
        Set{Symbol}(),
        Set{Symbol}(),
        Set{Symbol}(),
        Dict{Symbol,Set{Symbol}}(),
        Ref{Union{Nothing,Symbol}}(nothing),
        args,
        Set{Symbol}(),
        Set{Symbol}(),
    )
end
function mark_lhs_symbol!(state::DataflowAnalysisState, sym::Symbol)
    # Record that we've seen `sym` on the LHS of a tilde or as a generated quantity name
    push!(state.lhs_syms, sym)
    return nothing
end
function mark_symbol_used!(state::DataflowAnalysisState, syms::Set{Symbol})
    # Record that we've used `syms` in a later expression. In general, 'use' means
    # that the symbol may have been both written to and read from.
    used_lhs_syms = intersect(state.lhs_syms, syms)
    enclosing_gq = state.enclosing_gq[]
    if enclosing_gq === nothing
        union!(state.required_syms, used_lhs_syms)
    else
        union!(get!(Set{Symbol}, state.gq_uses, enclosing_gq), used_lhs_syms)
    end
    args = intersect(state.args, syms)
    union!(state.dirty_args, args)
    union!(state.args_to_copy, args)
    return nothing
end
function mark_as_written_to!(state::DataflowAnalysisState, syms::Set{Symbol})
    # Record that we've written to `syms` in a later expression. This is a special case for
    # the lhs of Sample statements which we know are only written to, not read from.
    union!(state.dirty_args, intersect(state.args, syms))
    return nothing
end
function mark_as_read_from!(state::DataflowAnalysisState, syms::Set{Symbol})
    # Record that we've read from `syms` in a later expression. This is a special case for
    # the lhs of Observe statements which we know are only read from, not written to.
    union!(state.required_syms, intersect(state.lhs_syms, syms))
    union!(state.args_to_copy, intersect(state.dirty_args, syms))
    return nothing
end

parse_variables!(::Any, ::DataflowAnalysisState) = nothing # e.g. literal
parse_variables!(::T, ::DataflowAnalysisState) where {T<:AbstractWrenExpr} =
    _issue_error("unhandled node of type $(T) in dataflow analysis")
parse_variables!(::LineNumberNode, ::DataflowAnalysisState) = nothing
function parse_variables!(sym::Symbol, state::DataflowAnalysisState)
    mark_symbol_used!(state, Set([sym]))
    return nothing
end
function parse_variables!(expr::Expr, state::DataflowAnalysisState)
    # Raw Julia expressions, e.g. inside `OtherStatement`s or `@batch` loop iterators.
    used = get_used_symbols(expr)
    # TODO(penelopeysm): This is a very conservative analysis because it assumes that
    # any appearance of a symbol in an expression counts as BOTH a write and a read. This
    # can happen in, for example,
    #
    #  f(x, y) = x .= y; return x
    #
    # where `x` is written to and then subsequently read from. This is kind of pathological
    # but sadly we have to be safe in the presence of arbitrary Julia code.
    mark_symbol_used!(state, used)
    return nothing
end
function parse_variables!(stmt::Sample, state::DataflowAnalysisState)
    # In e.g. `x[i] ~ y`, `i` and `y` are considered uses, so we need to check both lhs and
    # rhs. However `x` itself is not considered used since it's only written to.
    used = union(get_lhs_index_symbols(stmt.lhs), get_used_symbols(stmt.rhs))
    mark_symbol_used!(state, used)
    # TODO(penelopeysm): Appearing on the LHS of a Sample statement doesn't necessarily mean
    # that the symbol is written to, since it might have been conditioned on. So this is
    # overly conservative. See https://github.com/JuliaBayes/Wren.jl/issues/139.
    #
    # Note: in the case where it's conditioned on, the symbol isn't read from because Wren
    # will read from the `model.conditioned` NamedTuple instead. This might change if #139 is
    # implemented.
    mark_as_written_to!(state, Set([stmt.lhs_top_level_symbol]))
    # Record the top-level LHS symbol itself.
    mark_lhs_symbol!(state, stmt.lhs_top_level_symbol)
    push!(state.sample_syms, stmt.lhs_top_level_symbol)
    return nothing
end
function parse_variables!(stmt::Observe, state::DataflowAnalysisState)
    lhs_used = get_used_symbols(stmt.lhs)
    rhs_used = get_used_symbols(stmt.rhs)
    # LHS is only read from, but RHS can in general be either.
    mark_as_read_from!(state, lhs_used)
    mark_symbol_used!(state, rhs_used)
    return nothing
end
function parse_variables!(stmt::IID, state::DataflowAnalysisState)
    parse_variables!(stmt.tilde, state)
    parse_variables!(stmt.size, state)
    return nothing
end
function parse_variables!(stmt::Batch, state::DataflowAnalysisState)
    # TODO(penelopeysm): Inside the for loop, we know that the loop index is a new symbol,
    # so uses of it inside the loop body should not be considered as reusing a top-level
    # symbol. However, the chance that the loop index shadows a top-level symbol is pretty
    # low, so we can ignore this for now.
    parse_variables!(stmt.loop_iters, state)
    parse_variables!(stmt.size, state)
    parse_variables!(stmt.body, state)
    return nothing
end
function parse_variables!(stmt::AddLogLikelihood, state::DataflowAnalysisState)
    parse_variables!(stmt.expr, state)
    return nothing
end
function parse_variables!(stmt::GeneratedQuantity, state::DataflowAnalysisState)
    state.enclosing_gq[] = stmt.name
    parse_variables!(stmt.expr, state)
    state.enclosing_gq[] = nothing
    mark_lhs_symbol!(state, stmt.name)
    push!(state.gq_syms, stmt.name)
    return nothing
end
function parse_variables!(stmt::ReturnStatement, state::DataflowAnalysisState)
    parse_variables!(stmt.expr, state)
    return nothing
end
function parse_variables!(stmt::OtherStatement, state::DataflowAnalysisState)
    parse_variables!(stmt.expr, state)
    return nothing
end
function parse_variables!(expr::WrenExpr, state::DataflowAnalysisState)
    # TODO(penelopeysm): This is very generic and thus suboptimal. For example:
    #
    #  - `x = 2` will reassign to 2 and thus `x` should not be considered as reused.
    #
    #  - if/elseif/else branches are mutually exclusive, so uses of a symbol in the if
    #    branch should not be considered as reusing a symbol in the else branch. e.g.
    #
    #        @wren function g()
    #            if x
    #                a ~ Normal()
    #            else
    #                b = a  # Should not count as a use of `a` in the if branch.
    #            end
    #        end
    #
    # We could definitely do better here. However, the current implementation is still
    # technically correct, just a bit conservative - so we can leave the optimisations to
    # the future.
    for arg in expr.args
        parse_variables!(arg, state)
    end

    # For and while loop bodies have to be traversed twice to make sure we pick up edges
    # between different iterations of the loop. See e.g. discussion in
    # https://github.com/JuliaBayes/Wren.jl/pull/124.
    if expr.head === :for
        # For a `for` loop, the loop iters (`expr.args[1]`) are only evaluated once at the
        # beginning of the loop, so we can skip it.
        for arg in expr.args[2:end]
            parse_variables!(arg, state)
        end
    elseif expr.head === :while
        # For a `while` loop the condition is evaluated on every iteration so we need to
        # include it.
        for arg in expr.args
            parse_variables!(arg, state)
        end
    end
    return nothing
end

struct DataflowAnalysisResult
    required_syms::Set{Symbol}
    # For each generated quantity that is not required, the other generated quantities
    # whose evaluation needs its value
    gq_dependents::Dict{Symbol,Vector{Symbol}}
end

reconstruct_statement(@nospecialize(x::Any), ::DataflowAnalysisResult) = x
reconstruct_statement(::T, ::DataflowAnalysisResult) where {T<:AbstractWrenExpr} =
    _issue_error("unhandled node of type $(T) in reconstruct_statement")
function reconstruct_statement(stmt::Sample, result::DataflowAnalysisResult)
    lhs_is_reused = stmt.lhs_top_level_symbol in result.required_syms
    return Accessors.@set stmt.lhs_is_reused = lhs_is_reused
end
reconstruct_statement(stmt::Observe, ::DataflowAnalysisResult) = stmt
# The expression of a GeneratedQuantity cannot contain Samples.
function reconstruct_statement(stmt::GeneratedQuantity, result::DataflowAnalysisResult)
    name_is_reused = stmt.name in result.required_syms
    dependent_gqs = get(result.gq_dependents, stmt.name, Symbol[])
    return GeneratedQuantity(stmt.name, stmt.expr, name_is_reused, dependent_gqs)
end
# The contents of an OtherStatement are not lowered, so they can't contain Samples.
reconstruct_statement(stmt::OtherStatement, ::DataflowAnalysisResult) = stmt
function reconstruct_statement(stmt::IID, result::DataflowAnalysisResult)
    return Accessors.@set stmt.tilde = reconstruct_statement(stmt.tilde, result)
end
function reconstruct_statement(stmt::Batch, result::DataflowAnalysisResult)
    return Accessors.@set stmt.body = reconstruct_statement(stmt.body, result)
end
function reconstruct_statement(stmt::AddLogLikelihood, result::DataflowAnalysisResult)
    return Accessors.@set stmt.expr = reconstruct_statement(stmt.expr, result)
end
function reconstruct_statement(stmt::ReturnStatement, result::DataflowAnalysisResult)
    return Accessors.@set stmt.expr = reconstruct_statement(stmt.expr, result)
end
function reconstruct_statement(expr::WrenExpr, result::DataflowAnalysisResult)
    new_args = map(arg -> reconstruct_statement(arg, result), expr.args)
    return WrenExpr(expr.head, new_args)
end

# A generated quantity is required if a statement other than a generated quantity uses it,
# or if a required generated quantity uses it. Uses inside generated quantities are
# recorded in `gq_uses` during the traversal, and then propagated from the required
# generated quantities in a flood fill.
function analyse_dataflow(
    stmts::Vector{Union{AbstractWrenExpr,LineNumberNode}},
    args::Set{Symbol},
)
    state = DataflowAnalysisState(args)
    for stmt in stmts
        parse_variables!(stmt, state)
    end
    # Flood fill: everything used by a required generated quantity is required too.
    frontier = collect(intersect(state.required_syms, state.gq_syms))
    while !isempty(frontier)
        gq = pop!(frontier)
        for sym in get(state.gq_uses, gq, ())
            if !(sym in state.required_syms)
                push!(state.required_syms, sym)
                sym in state.gq_syms && push!(frontier, sym)
            end
        end
    end
    union!(state.skippable_gqs, setdiff(state.gq_syms, state.required_syms))
    # A skippable generated quantity is only evaluated alongside the generated quantities
    # that depend on it, but any sampled variable it uses must always be bound.
    for used_syms in values(state.gq_uses)
        union!(state.required_syms, intersect(used_syms, state.sample_syms))
    end
    if WREN_COMPILATION_DEBUG[]
        @info "[dataflow.jl] lhs_syms = $(state.lhs_syms)"
        @info "[dataflow.jl] required_syms = $(state.required_syms)"
        @info "[dataflow.jl] gq_uses = $(state.gq_uses)"
        @info "[dataflow.jl] args_to_copy = $(state.args_to_copy)"
    end
    return state
end

function get_required_syms_and_args(
    stmts::Vector{Union{AbstractWrenExpr,LineNumberNode}},
    args::Set{Symbol},
)
    state = analyse_dataflow(stmts, args)
    return state.required_syms, state.args_to_copy
end

# The dependents of `gq` are the generated quantities whose expressions use `gq`, directly
# or through other skippable generated quantities.
function get_gq_dependents(state::DataflowAnalysisState)
    gq_dependents = Dict{Symbol,Vector{Symbol}}()
    for gq in state.skippable_gqs
        dependents = Set{Symbol}()
        frontier = [gq]
        while !isempty(frontier)
            used_gq = pop!(frontier)
            for (user_gq, used_syms) in state.gq_uses
                if used_gq in used_syms && user_gq != gq && !(user_gq in dependents)
                    push!(dependents, user_gq)
                    push!(frontier, user_gq)
                end
            end
        end
        gq_dependents[gq] = sort!(collect(dependents))
    end
    return gq_dependents
end

function run_dataflow_analysis(
    stmts::Vector{Union{AbstractWrenExpr,LineNumberNode}},
    args::Set{Symbol},
)
    state = analyse_dataflow(stmts, args)
    result = DataflowAnalysisResult(state.required_syms, get_gq_dependents(state))
    new_stmts = map(stmt -> reconstruct_statement(stmt, result), stmts)
    return Vector{Union{AbstractWrenExpr,LineNumberNode}}(new_stmts), state.args_to_copy
end
