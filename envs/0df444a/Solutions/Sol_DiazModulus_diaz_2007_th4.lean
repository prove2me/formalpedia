-- Prove2me | solution 1 for DiazModulus.diaz_2007_th4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:54:41.93563+00:00
-- url     : https://prove2.me/submissions/75c0fb06-9376-438c-babd-ed4ae75f0c37

import Mathlib
import Definitions.Def_DiazModulus

/-!
# Diaz 2007, Théorème 4

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres
algébriques*, JTNB 19 (2007), Théorème 4 (pp. 385–388).

`hSSE` is Roy's strong six exponentials theorem: for `Q̄`-linearly independent
`x : Fin 2 → ℂ` and `y : Fin 3 → ℂ`, not every product `x i * y j` lies in `ℒ̃`.
`hB` is Baker's theorem for two logarithms: a non-trivial `Q̄`-combination of two `ℚ`-free
elements of `ℒ` is transcendental.

* **1)** Apply `hSSE` to `x = (x₁, x₂)` and `y = (y₁, y₂, 1/x₁)`; `x₁ ≠ 0` by freeness. The six
  products are the four given ones, `x₁ · (1/x₁) = 1 ∈ ℒ̃` and `x₂ · (1/x₁) = x₂/x₁ ∈ ℒ̃`.
* **2)** Suppose the four products lie in `ℒ`.
  - `(x₁y₁, x₂y₁)` is a `ℚ`-free pair in `ℒ`, as `x` is `ℚ`-free and `y₁ ≠ 0`. A relation
    `a x₁ + b x₂ = 0` over `Q̄`, times `y₁`, makes `a x₁y₁ + b x₂y₁ = 0`, which `hB` forbids
    unless `a = b = 0`. So `(x₁, x₂)` is `Q̄`-free.
  - `(x₁y₁, x₁y₂)` is a `ℚ`-free pair in `ℒ`, as `y` is `ℚ`-free and `x₁ ≠ 0`. A relation
    `a y₁ + b y₂ + c/x₁ = 0`, times `x₁`, makes `a x₁y₁ + b x₁y₂ = -c` algebraic, so `hB`
    forces `a = b = 0`, and then `c = 0`. So `(y₁, y₂, 1/x₁)` is `Q̄`-free.
  - Part 1 then gives the contradiction, because `ℒ ⊆ ℒ̃`.
-/

open Complex ComplexConjugate

namespace D6_diaz_2007_th4

open DiazModulus

/-- `1 ∈ ℒ̃`. -/
theorem one_mem_logAlgTilde : (1 : ℂ) ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

/-- `ℒ ⊆ ℒ̃`. -/
theorem mem_logAlgTilde_of_mem_logAlg {z : ℂ} (h : z ∈ LogAlg) : z ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

/-- A pair that is free over `Q̄` in the elementwise form is `Q̄`-linearly independent. -/
theorem linearIndependent_pair {x₁ x₂ : ℂ}
    (h : ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * x₁ + b * x₂ = 0 → a = 0 ∧ b = 0) :
    LinearIndependent (↥Qbar) ![x₁, x₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨hs, ht⟩ := h s t s.2 t.2 hst
  exact ⟨Subtype.ext hs, Subtype.ext ht⟩

/-- A triple that is free over `Q̄` in the elementwise form is `Q̄`-linearly independent. -/
theorem linearIndependent_triple {y₁ y₂ y₃ : ℂ}
    (h : ∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * y₁ + b * y₂ + c * y₃ = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    LinearIndependent (↥Qbar) ![y₁, y₂, y₃] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  have hg' : (g 0 : ℂ) * y₁ + (g 1 : ℂ) * y₂ + (g 2 : ℂ) * y₃ = 0 := hg
  obtain ⟨h0, h1, h2⟩ := h _ _ _ (g 0).2 (g 1).2 (g 2).2 hg'
  intro i
  fin_cases i
  exacts [Subtype.ext h0, Subtype.ext h1, Subtype.ext h2]

end D6_diaz_2007_th4

open DiazModulus D6_diaz_2007_th4 in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    -- 1)
    (∀ x₁ x₂ y₁ y₂ : ℂ,
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * x₁ + b * x₂ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * y₁ + b * y₂ + c * (1 / x₁) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      x₂ / x₁ ∈ LogAlgTilde →
      ¬ (x₁ * y₁ ∈ LogAlgTilde ∧ x₁ * y₂ ∈ LogAlgTilde ∧ x₂ * y₁ ∈ LogAlgTilde ∧ x₂ * y₂ ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ x₁ x₂ y₁ y₂ : ℂ,
      (∀ p q : ℚ, (p : ℂ) * x₁ + (q : ℂ) * x₂ = 0 → p = 0 ∧ q = 0) →
      (∀ p q : ℚ, (p : ℂ) * y₁ + (q : ℂ) * y₂ = 0 → p = 0 ∧ q = 0) →
      x₂ / x₁ ∈ LogAlgTilde →
      ¬ (x₁ * y₁ ∈ LogAlg ∧ x₁ * y₂ ∈ LogAlg ∧ x₂ * y₁ ∈ LogAlg ∧ x₂ * y₂ ∈ LogAlg)) := by
  -- 1) `hSSE` on `x = (x₁, x₂)`, `y = (y₁, y₂, 1/x₁)`
  have part1 : ∀ x₁ x₂ y₁ y₂ : ℂ,
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * x₁ + b * x₂ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * y₁ + b * y₂ + c * (1 / x₁) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      x₂ / x₁ ∈ LogAlgTilde →
      ¬ (x₁ * y₁ ∈ LogAlgTilde ∧ x₁ * y₂ ∈ LogAlgTilde ∧ x₂ * y₁ ∈ LogAlgTilde ∧
        x₂ * y₂ ∈ LogAlgTilde) := by
    intro x₁ x₂ y₁ y₂ hx hy hq ⟨h11, h12, h21, h22⟩
    have hx₁ : x₁ ≠ 0 := fun h0 =>
      one_ne_zero (hx 1 0 Qbar.one_mem Qbar.zero_mem (by rw [h0]; ring)).1
    refine hSSE ![x₁, x₂] ![y₁, y₂, 1 / x₁] (linearIndependent_pair hx)
      (linearIndependent_triple hy) ?_
    intro i j
    fin_cases i <;> fin_cases j
    · exact h11
    · exact h12
    · show x₁ * (1 / x₁) ∈ LogAlgTilde
      rw [mul_one_div_cancel hx₁]
      exact one_mem_logAlgTilde
    · exact h21
    · exact h22
    · show x₂ * (1 / x₁) ∈ LogAlgTilde
      rwa [mul_one_div]
  refine ⟨part1, ?_⟩
  -- 2) both freeness hypotheses of part 1 come from `hB`
  intro x₁ x₂ y₁ y₂ hx hy hq ⟨h11, h12, h21, h22⟩
  have hx₁ : x₁ ≠ 0 := fun h0 => one_ne_zero (hx 1 0 (by rw [h0]; simp)).1
  have hy₁ : y₁ ≠ 0 := fun h0 => one_ne_zero (hy 1 0 (by rw [h0]; simp)).1
  -- `(x₁ y₁, x₂ y₁)` is `ℚ`-free
  have hcol : ∀ p q : ℚ, (p : ℂ) * (x₁ * y₁) + (q : ℂ) * (x₂ * y₁) = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    refine hx p q ((mul_eq_zero.1 ?_).resolve_right hy₁)
    linear_combination hpq
  -- `(x₁ y₁, x₁ y₂)` is `ℚ`-free
  have hrow : ∀ p q : ℚ, (p : ℂ) * (x₁ * y₁) + (q : ℂ) * (x₁ * y₂) = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    refine hy p q ((mul_eq_zero.1 ?_).resolve_left hx₁)
    linear_combination hpq
  refine part1 x₁ x₂ y₁ y₂ ?_ ?_ hq
    ⟨mem_logAlgTilde_of_mem_logAlg h11, mem_logAlgTilde_of_mem_logAlg h12,
      mem_logAlgTilde_of_mem_logAlg h21, mem_logAlgTilde_of_mem_logAlg h22⟩
  · -- `(x₁, x₂)` is `Q̄`-free: `a x₁y₁ + b x₂y₁ = 0` is algebraic
    intro a b ha hb hab
    by_contra hne
    refine hB (x₁ * y₁) (x₂ * y₁) a b h11 h21 hcol (mem_Qbar_iff.1 ha) (mem_Qbar_iff.1 hb)
      hne ?_
    have e : a * (x₁ * y₁) + b * (x₂ * y₁) = 0 := by linear_combination y₁ * hab
    rw [e]
    exact isAlgebraic_zero
  · -- `(y₁, y₂, 1/x₁)` is `Q̄`-free: `a x₁y₁ + b x₁y₂ = -c` is algebraic
    intro a b c ha hb hc habc
    have hab : a = 0 ∧ b = 0 := by
      by_contra hne
      refine hB (x₁ * y₁) (x₁ * y₂) a b h11 h12 hrow (mem_Qbar_iff.1 ha) (mem_Qbar_iff.1 hb)
        hne ?_
      have e : a * (x₁ * y₁) + b * (x₁ * y₂) = -c := by
        linear_combination x₁ * habc - c * mul_one_div_cancel hx₁
      rw [e]
      exact (mem_Qbar_iff.1 hc).neg
    obtain ⟨rfl, rfl⟩ := hab
    refine ⟨rfl, rfl, (mul_eq_zero.1 ?_).resolve_right (one_div_ne_zero hx₁)⟩
    linear_combination habc
