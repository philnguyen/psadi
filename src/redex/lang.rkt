#lang racket
(provide (all-defined-out))
(require redex)

(define-language L
  ;; Syntax
  [#|Expressions      |# e ::= x l (e e) (set! x e)]
  [#|Function literals|# l ::= (λ x e)]
  [#|Variables        |# x y z ::= variable-not-otherwise-mentioned]
  [#|Source Locations |# ℓ ::= integer]

  ;; Semantics
  [#|Values          |# u ::= #|Transparent|# (Clo l ρ)
                              #|Symbolic   |# (↝ x ...)]
  [#|Abstract Values |# v ::= {(u if φ) ...}]
  [#|Environments    |# ρ ::= {[x ↦ α] ...}]
  [#|Addresses       |# α ::= #|Transaprent|# (x @ ℓ ...)
                              #|Symbolic   |# (↝ x ...)]
  [#|Stores          |# σ ::= {[α ↝ v] ...}]
  [#|Path conditions |# φ ::= {[u : l] ...}]
  [                    ?φ ::= φ #f]
  [#|Summary Tables  |# Σ ::= {[l ⇒ s] ...}] ; ≃ "memo-table" in original ADI
  [#|Summaries       |# s ::= (v σ) #f])

(define-judgment-form L
  #:contract (⊢ Σ : Σ σ : e ⇓ v σ Σ)
  #:mode     (⊢ I I I I I I I O O O)

  ;; `(x @)` is always the symbolic address variable `x` maps to when in scope
  [-----------------------------------------"ev-var"
   (⊢ _ : Σ σ : x ⇓ (lookup-σ σ (↝ x)) σ Σ)]

  [(where {x ...} (fv l))
   (where ρ {[x ↦ (↝ x)] ...})
   -----------------------------------------"ev-lam"
   (⊢ _ : Σ σ : l ⇓ (Clo l ρ) σ Σ)]

  [(⊢ Σ_in : Σ_0 σ_0 : e ⇓ v σ_1 Σ_1)
   -----------------------------------------"ev-set"
   (⊢ Σ_in : Σ_0 σ_0 : (set! x e) ⇓ v (⊔σ σ_1 {[(↝ x) ↝ v]}) Σ_1)]

  [(⊢ Σ_in : Σ_0 σ_0 : e_1 ⇓ v_1 σ_1 Σ_1)
   (⊢ Σ_in : Σ_1 σ_1 : e_2 ⇓ v_2 σ_2 Σ_2)
   (where ℓ ,(ℓ! (term (e_1 e_2))))
   (⊢ᵃ* Σ_in : Σ_2 σ_2 ℓ : v_1 v_2 ⇓ v_a σ_a Σ_a)
   -----------------------------------------"ev-app"
   (⊢ Σ_in : Σ_0 σ_0 : (e_1 e_2) ⇓ v_a σ_a Σ_a)]
  )

(define-judgment-form L
  #:contract (⊢ᵃ* Σ : Σ σ ℓ : v v ⇓ v σ Σ)
  #:mode     (⊢ᵃ* I I I I I I I I I O O O)

  [-----------------------------------------"app-none"
   (⊢ᵃ* _ : Σ σ _ : {} _ ⇓ {} σ Σ)]

  [(where v_x* (refine-v v_x φ))
   (⊢ᵃ Σ_in : Σ_0 σ_0 ℓ : u v_x* ⇓ v_1 σ_1 Σ_1)
   (⊢ᵃ* Σ_in : Σ_1 σ_0 ℓ : {any_i ...} v_x ⇓ v_i σ_i Σ_i)
   -----------------------------------------"app-some"
   (⊢ᵃ* Σ_in : Σ_0 σ_0 ℓ : {(u if φ) any_i ...} v_x ⇓ (⊔v v_1 v_x) (⊔σ σ_1 σ_i) Σ_i)])

(define-judgment-form L
  #:contract (⊢ᵃ Σ : Σ σ ℓ : u v ⇓ v σ Σ)
  #:mode     (⊢ᵃ I I I I I I I I I O O O)

  [(⊢/memo Σ_in : Σ_0 : l ⇓ v_ee σ_ee Σ_1)
   (where α_x (x @))
   (where σ_er* (⊔σ σ_er {[α_x ↝ v]}))
   (where ρ_* (⧺ ρ {[x ↦ α_x]}))
   (⊢ᵛ σ_er* ρ_* : (tick-v ℓ v_ee) ⟹ v_a)
   (⊢ˢ σ_er* ρ_* : (tick-σ ℓ σ_ee) ⟹ σ_a)
   -----------------------------------------"app-lam"
   (⊢ᵃ Σ_in : Σ_0 σ_er ℓ : (Clo l ρ) v ⇓ v_a (⊔σ σ_er* σ_a) Σ_1)]

  [(where {_ ... [(name l (λ x e)) ⇒ _] _ ...} Σ_0)
   (where v_x (refine-v v {[z : l]}))
   (⊢/memo Σ_in : Σ_0 : l ⇓ v_ee σ_ee Σ_1)
   (where α_x (x @))
   (where σ_er* (⊔σ σ_er {[α_x ↝ v_x]}))
   (where {y ...} (fv l))
   (where ρ_* {[y ↦ (↝ z ... y)] ... [x ↦ α_x]})
   (⊢ᵛ σ_er* ρ_* : (reroot-v z (tick-v ℓ v_ee)) ⟹ v_a)
   (⊢ˢ σ_er* ρ_* : (reroot-σ z (tick-σ ℓ σ_ee)) ⟹ σ_a)
   -----------------------------------------"app-sym"
   (⊢ᵃ Σ_in : Σ_0 σ_er ℓ : (↝ z ...) v ⇓ v_a (⊔σ σ_er* σ_a) Σ_1)]
  )

(define-judgment-form L
  #:contract (⊢ᵛ σ ρ : v ⟹ v)
  #:mode     (⊢ᵛ I I I I I O)

  [-----------------------------------------"btm"
   (⊢ᵛ _ _ : {} ⟹ {})]

  [(⊢ᵠ σ ρ : φ ⟹ φ_1)
   (⊢ᵘ σ ρ : u ⟹ u_1)
   (⊢ᵛ σ ρ : {any_i ...} ⟹ v_i)
   -----------------------------------------"join"
   (⊢ᵛ σ ρ : {(u if φ) any_i ...} ⟹ (⊔v {(u_1 if φ_1)} v_i))]

  [(⊢ᵠ σ ρ : φ ⟹ #f)
   (⊢ᵘ σ ρ : u ⟹ u_1)
   (⊢ᵛ σ ρ : {any_i ...} ⟹ v_i)
   -----------------------------------------"drop"
   (⊢ᵛ σ ρ : {(u if φ) any_i ...} ⟹ v_i)]
  )

(define-judgment-form L
  #:contract (⊢ᵠ σ ρ : φ ⟹ ?φ)
  #:mode     (⊢ᵠ I I I I I O)
  [(⊢ᵘ σ ρ : u ⟹ u_1) ...
   -----------------------------------------
   (⊢ᵠ σ ρ : {[u : l] ...} ⟹ (refine-φ {[u_1 : l]} ...))])

(define-judgment-form L
  #:contract (⊢ˢ σ ρ : σ ⟹ σ)
  #:mode     (⊢ˢ I I I I I O)
  [(⊢ᵅ σ ρ : α ⟹ α_1) ...
   (⊢ᵘ σ ρ : u ⟹ u_1) ...
   -----------------------------------------
   (⊢ˢ σ ρ : {[α ↝ v] ...} ⟹ (⊔σ {[α_1 ↝ u_1]} ...))])

(define-judgment-form L
  #:contract (⊢ᵅ σ ρ : α ⟹ α)
  #:mode     (⊢ᵅ I I I I I O)

  [-----------------------------------------"free"
   (⊢ᵅ _ _ : (name α (x @ _ ...)) ⟹ α)]

  [-----------------------------------------"bound"
   (⊢ᵅ σ {_ ... [x ↦ α] _ ...} : (↝ x) ⟹ α)]

  [
   -----------------------------------------"chase"
   (⊢ᵅ σ ρ : (↝ x y ...) ⟹ )]
  )
