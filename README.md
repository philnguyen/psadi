Polymorphic Summaries for Abstract Definitional Interpreters
=========================================

[AAM](https://dl.acm.org/doi/10.1145/1863543.1863553)- and
[ADI](https://dl.acm.org/doi/10.1145/3110256)-based
analyses' faithfulness to operational semantics brings substantial benefits
(e.g. easy extension to expressive features with straightforward soundness proofs),
but also seems to inevitably carry over one downside:
each component is re-analyzed at each use, which either
enjoys precision when it works well, or duplicates imprecision and multiplies overhead
when it doesn't.
The lack of function summaries is a key hindrance in scaling these analyses to large codebases.

This **in progress** Redex model describes a re-formulation of ADI to produce
*polymorphic summaries*
that enables a scalable and precise analysis of incomplete higher-order stateful programs,
*using only a first-order language for summaries*.
Summaries for smaller units (e.g. functions, modules, etc.) can be used as-is when analyzing
arbitrary code without compromising soundness,
but can also be "linked" together for a more precise summary,
at a cost less than a from-scratch analysis.
What's more, ADI naturally yields *memoized top-down*, as opposed to bottom-up summarization,
avoiding the cost of analyzing the entire codebase when the entry point only reaches a
small fraction of the code.

High-level Ideas
-----------------------------------------

Initial idea: We want produce summaries by running each `λ` only once[^once],
*symbolically*, agnostic to any caller.
The *polymorphic summary* contains result, effect (e.g. "store delta"),
and path-condition in terms of the symbolic arguments.
Then at each call site, we instantiate the summary by substituting the actual arguments,
potentially eliminating spurious paths.
[^once]: Unless there's circular dependency, which is taken care of by ADI's cache-fixing loop.

The obvious problem with this idea is: *What should we do with symbolic functions?*

While it's tempting to try to come up with a language of "polymorphic, higher-order summaries"
similar to a type-and-effect system that somehow is decidable without resorting to trivial
imprecision, that's a very difficult route, especially for untyped languages and idioms.
Even if we managed to do it for a fixed set of
language features, the language of summaries would likely be far removed from the
operational semantics, making soundness proof and extension to new features challenging.

Another choice that would result in pessimal precision, despite soundness, is to use
[havoc](https://dl.acm.org/doi/10.1145/3158139)
to over-approximate all interactions with unknown code whenever in doubt.
For contract verification, the imprecision can be
mitigated with more precise contracts at boundaries (e.g. parametric contracts),
but that isn't viable for static analysis in general.

To combine *almost* the simplicity of mirroring the operational semantics,
the scalability of function summaries,
and the sound modularity from `havoc`, we make the following two observations:

1. Whole higher-order programs are essentially first-order programs
   (e.g. by defunctionalization).
   With the closed-world assumption, *higher-order functions only need first-order summaries*.

2. Incomplete programs are essentially whole programs, with unknown code filled in as `havoc`,
   with its own first-order summary.

### "Polymorphic", just not "parametric"

This work is inspired by the line of work on
[polymorphic method summaries for whole OO programs](https://web.eecs.umich.edu/~xwangsd/pubs/aplas15.pdf),
where it's valid to make the closed-world assumption that all implementations to each class
are known. At each virtual method invocation, the analysis simply gathers the summaries
of *all* known implementations,
then uses information at the call-site to discard spurious cases
or propagate constraints on the receiver's dynamic class tag.
The obtained "polymorphic" summaries are only valid in the specific whole program they're in,
and would be invalidated by additional method implementations.

For functional programs, this is analogous to analyzing their defunctionalized versions[^defunct].
Specifically, each `(λ x e)` form has a first-order summary of `e`'s result and effect
(as a *store delta*), with respect to a *symbolic environment* ranging over `e`'s free variables.
Each application's results and effects are gathered from the summaries of all known `λ`s,
each guarded by a constraint over the target closure's "`λ`-tag".
As long as the program is closed, the summaries are sound.
Summary instantiation is a straight-forward substitution of the symbolic environment with
the actual one from the target closure, with no further call to evaluation.
Summary instantiation is sensitive in the closure's `λ`-tag, its environment, and the argument.

[^defunct]: Although we don't need to explicitly defunctionalize the program.

Note that there is no such thing as "applying a symbolic function then obtaining its symbolic result
and effect" in this system, thanks to the "defunctionalized view".
When "in doubt", we case-split over all known `λ`s then use respective first-order summaries
guarded by constraints over the `λ`-tag.

Although it sounds expensive to consider all `λ`s in many cases, remember that we are
pumping memoized summaries around, not re-running analyses.

### Removing the closed-world assumption to enable modularity

Whole-program analyses are useful, and separating the *scalability* goal from the stronger
*modularity* goal is neat, but we sometimes need modularity, such as verifying a component
once and for all against arbitrary uses.

Luckily, there's
[previous work on soundly over-approximating unknown code in the presence of
higher-order functions and mutable states](https://dl.acm.org/doi/10.1145/3158139)
using an operation called `havoc`.
To generalize function summaries for incomplete programs, we simply add `havoc`'s summaries
for use when (1) applying a closure whose `λ`-tag is from the unknown,
and (2) when a `λ` from one module flows to another module that doesn't already "know" it.
As a result, we get *summaries that are sound even in an open world,
and also precise for known code*.

When analyzing code that uses both modules `m1` and `m2`, we could either re-use their
separately produced summaries as-is, or "link"[^link] those summaries by
re-running ADI's cache-fixing loop over the merged summaries and produce a more precise
summary of both `m1` and `m2`.

[^link]:The term "linking" only conveys a loose analogy, unfortunately:
we still need `m1` and `m2`'s source code to re-run ADI. But the process is cheaper
than re-running ADI from scratch.

### ADI for memoized top-down instead of bottom-up

Most work on function summaries present the process as eager bottom-up. As well understood from
dynamic programming, one drawback compared to (memoized) top-down is the potentially needless
computations when only a fraction of the codebase is reachable from the entry point.

ADI naturally carries out the semantics top-down memoized, starting from the entry
point. We track the `λ`s whose closures have been created, and only consider summaries for those,
on-demand, at applications. This potentially requires more iterations to reach a fix-point,
but can save lots of work when the reachable code is small compared to the entire codebase.

The Redex Model (NOT FINISHED!!)
-----------------------------------------

The Redex model is for a *modified concrete semantics that summarizes each function as
first-order values and store-deltas*.
This semantics should compute the same result as the standard operational semantics[^proof],
and can be systematically finitized (ala AAM/ADI) to obtain a static analysis.
The model is minimal and omits `havoc`.
The language is λ-calculus with `set!`.

[^proof]: TODO needs proof. But this can be done once, then all abstractions by finitization and non-determinism should be sound.

### *Symbolic* vs *transparent*

There's a distinction between *symbolic* and *transparent* addresses `α` and values `v`.
When analyzing a function:
* A *symbolic address* stands for one that is passed in from an arbitrary caller.
  All values and addresses initially reachable from it are also symbolic.
  No aliasing information is assumed.
* A *transparent address* is one allocated either directly within the function's body
  or indirectly from its callees. Aliasing among transparent addresses are always
  soundly tracked and approximated. In particular, transparent addresses cannot be aliased
  by symbolic addresses, by construction.
  
Unlike standard ADI, this system:
* only memoizes function bodies (as opposed to all sub-expressions)
* memoizes symbolic results to be instantiated at each call site
  (as opposed to already context-sensitive results to be returned as-is).
  
In this formalism, application is the only place where we allocate a transparent address.
Given the callee's result, we specialize it by:
* substituting its symbolic addresses with the caller's ones (with `⟹`)
* consistently renaming its transparent addresses by attaching the caller's context `ℓ`
  (with `tick`; the name is inspired by AAM's work, but its use is in contrast to classic AAM
  and ADI that propagates contexts from callers to callees.)
* doing the obvious constraint propagation, path pruning, and effect joining (with `⊔σ`).

### Path-condition representation

Instead of representing conditions per-path, we guard values (and therefore chunks
of effect) with smaller chunks of the path-condition, and take their conjunction at appropriate
places. This representation prevents eager splitting and duplicating of many constructs.

For example, `{[α₁ ↦ {v₁ if φ₁, v₂ if φ₂}] [α₂ ↦ {v₃ if φ₃, v₄ if φ₄}]}` compactly represents
many paths: `{[α₁ ↦ v₁, α₂ ↦ v₃] if φ₁ ∧ ¬φ₂ ∧ φ₃}`, `{[α₂ ↦ v₂, α₂ ↦ v₃] if ¬φ₁ ∧ φ₂ ∧ φ₃}`,
`{[α₂ ↦ {v₁, v₂}, α₂ ↦ v₃] if φ₁ ∧ φ₂ ∧ φ₃}`, etc.

The language of constraints in `φ` talks about (1) `λ`-tags of values and
(2) referential equality.

### Aliasing

Two symbolic closures (with the same `λ`-tag) can be aliases of each other,
which means if we execute one and get a `set!` effect at symbolic address `ρ₁[x]`,
it may or may not reflect in symbolic address `ρ₂[x]` when we run the other closure for the result.
For this reason, whenever we get back an effect `ρ₁[x] ↦ {v₁}`, we also include the conditional
effect `ρ₂[x] ↦ {v₁ if ρ₁ = ρ₂}`.

### Unbounded components in the concrete summarizing semantics, and their abstractions

Two components can grow unboundedly:
1. Transparent addresses with accumulated contexts: callers can keep attaching new contexts
   to callee's returned transparent addresses to distinguish results from different call sites.
2. Symbolic addresses growing access paths (e.g. `ρ[x]->y->x->y->...`)

We apply AAM/ADI-style finitization:
1. For transparent addresses, we coudld either do fixed `k`,
   or approximate the list with a set (which is finite in any program).
   Note that we can't multiply analysis contexts no matter what choice.
   We only risk having poorly summarized results.
2. For symbolic addresses,
   we can store-allocate the access paths to effectively summarize unbounded chains
   using a regular language, that reflects the program's structure.

While abstract addresses with cardinality >1 cannot be refined in constraints,
when instantiating a summary with them as arguments and a summary case specifies
a completely disjoint set of values for the corresonding parameter,
that's still a spurious case to be discarded.

Possible Optimizations
-----------------------------------------

### Abstract garbage collection

This work is very amenable to
[stack-independent abstract GC](https://kimball.germane.net/germane-2019-stack-liberated.pdf)
and reference counting to support
strong updates of transparent addresses.
The GC is done locally per function, over a relatively small store-delta and root set.

### Lock-free parallelism
