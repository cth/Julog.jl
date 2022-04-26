## PRISM-like probabilistic extensions
"""
     prism_choices_augmentation(clause)

     Construct copy of `clause`, which includes an additional argument (placed last) to collect probabilistic 
     choices made during the execution, i.e., when resolving a goal.

     Upon resolution, the added argument will be a ground term on the form:
     `choices(Arg_1, ..., Arg_N)` where `N` is the number of subgoals in the body
     of the clause used to resolve the goal. Any argument `Arg_i` (1 <= i <= N) may be: 
        a) an term `msw(id, outcome, probability_of_outcome)` for an msw subgoal
        b) a variable to capture probabilistic choices made by a non-msw subgoal - this is through
           unification as this variable is also appended as an additional argument to the subgoal.
        c) a `nonprism` term (no arguments) for facts (N=0)

    The `choices` term represents a tree structure that includes all probabilistic choices
    made to prove a given goal using if `prism_choice_augmentation!` is applied to all
    clauses in Julog embedded PRISM program. Broadcasting, i.e., `prism_choice_augmentation!.(clauses)`
    is useful to apply to an entire PRISM program.
"""
function prism_choices_augmentation(c::Clause)::Clause
    cl = deepcopy(c)
    var_ctr = 0
    nextvar() = Var(Symbol("MSW$(var_ctr=var_ctr+1)"))
    choices = Compound(:choices, Vector{Term}())
    for t in cl.body
        if t.name == :msw
            if length(t.args)==2
                push!(t.args, nextvar())
                push!(choices.args,t)
            elseif length(t.args)==3
                @assert isa(t.args[3],Var)
                push!(choices.args,t)
            end
        elseif t.name in Julog.builtins
            continue
        else
            push!(t.args,nextvar())
            push!(choices.args,last(t.args))
        end
    end
    if length(choices.args)==0
        choices.name==:nonprism
    end
    if !(cl.head.name in Julog.builtins)
        push!(cl.head.args,choices)
    end
    return cl
end

prism_example1 = @julog [
    values(tr(X),[1,2,3]) <<= true, set_sw(tr(a),[1.0,0,0]) <<= true,
    other(P) <<= msw(tr(1),X,P),
    top(X,O) <<= msw(tr(X),O) & other(_) & msw(tr(Y),O)
]

prism_example_dna_sequence = @julog [
    values(dna,[a,g,c,t]) <<= true,
    dnaseq(0,[]) <<= cut,
    dnaseq(N,[X|Xs]) <<= msw(dna,X) & dnaseq(N-1,Xs)
]

prism_example_interaction = @julog [
    values(a,[1,2,3]) <<= true,
    set_sw(a,[0.6,0.3,0.1]) <<= true,
    interaction(Z) <<= msw(a,X,P1) & msw(a,Y,P2) & is(P,P1*P2) & P>0.05
]