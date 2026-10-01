-- Prove2me | solution 1 for DiazModulus.strong_six_exponentials_iff_quotient_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:17:41.65295+00:00
-- url     : https://prove2.me/submissions/22a00cf3-7702-4b56-8a8a-b4878f3a7610

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace QuotientForm

open DiazModulus

/-- `Qbar`-independence of `x : Fin 2 → ℂ`, read off on complex coefficients. -/
theorem indep_two {x : Fin 2 → ℂ} (hx : LinearIndependent (↥Qbar) x) {a b : ℂ}
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : a * x 0 + b * x 1 = 0) : a = 0 ∧ b = 0 := by
  have hg := Fintype.linearIndependent_iff.1 hx ![⟨a, ha⟩, ⟨b, hb⟩]
    (by rw [Fin.sum_univ_two]; exact h)
  exact ⟨congrArg Subtype.val (hg 0), congrArg Subtype.val (hg 1)⟩

/-- `Qbar`-independence of `y : Fin 3 → ℂ`, read off on complex coefficients. -/
theorem indep_three {y : Fin 3 → ℂ} (hy : LinearIndependent (↥Qbar) y) {a b c : ℂ}
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (h : a * y 0 + b * y 1 + c * y 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hg := Fintype.linearIndependent_iff.1 hy ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
    (by rw [Fin.sum_univ_three]; exact h)
  exact ⟨congrArg Subtype.val (hg 0), congrArg Subtype.val (hg 1), congrArg Subtype.val (hg 2)⟩

end QuotientForm

open DiazModulus QuotientForm in
/-- G. Diaz, JTNB 19 (2007), Théorème 3, versions 1 ⇔ 3: the strong six exponentials statement
for `2 × 3` matrices is equivalent to its quotient form in four elements `l₀, …, l₃` of `ℒ̃`.
The dictionary is `x = (1, l₁/l₀)`, `y = (l₀, l₂, l₃)` one way, and
`l₀ = x₀y₀`, `l₁ = x₁y₀`, `l₂ = x₀y₁`, `l₃ = x₀y₂` the other. -/
theorem solution :
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) ↔
    (∀ l₀ l₁ l₂ l₃ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      l₃ ∈ LogAlgTilde →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₀ + b * l₁ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * l₃ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ / l₀ ∈ LogAlgTilde ∧ l₁ * l₃ / l₀ ∈ LogAlgTilde)) := by
  constructor
  · -- version 1 ⇒ version 3, on the matrix `x = (1, l₁/l₀)`, `y = (l₀, l₂, l₃)`
    rintro V1 l₀ l₁ l₂ l₃ h0 h1 h2 h3 h01 h023 ⟨hq2, hq3⟩
    have hl0 : l₀ ≠ 0 := by
      intro hz
      exact one_ne_zero (h01 1 0 (one_mem _) (zero_mem _) (by rw [hz]; ring)).1
    refine V1 ![1, l₁ / l₀] ![l₀, l₂, l₃] ?_ ?_ ?_
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have hst' : (s : ℂ) * 1 + (t : ℂ) * (l₁ / l₀) = 0 := hst
      have hrel : (s : ℂ) * l₀ + (t : ℂ) * l₁ = 0 := by
        have e : (s : ℂ) * l₀ + (t : ℂ) * l₁ = l₀ * ((s : ℂ) * 1 + (t : ℂ) * (l₁ / l₀)) := by
          field_simp
        rw [e, hst', mul_zero]
      obtain ⟨hs, ht⟩ := h01 s t s.2 t.2 hrel
      exact ⟨Subtype.ext hs, Subtype.ext ht⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      have hrel : (g 0 : ℂ) * l₀ + (g 1 : ℂ) * l₂ + (g 2 : ℂ) * l₃ = 0 := by
        rw [Fin.sum_univ_three] at hg
        exact hg
      obtain ⟨ha, hb, hc⟩ := h023 _ _ _ (g 0).2 (g 1).2 (g 2).2 hrel
      intro i
      fin_cases i
      exacts [Subtype.ext ha, Subtype.ext hb, Subtype.ext hc]
    · intro i j
      fin_cases i <;> fin_cases j
      · simpa using h0
      · simpa using h2
      · simpa using h3
      · simpa [div_mul_cancel₀ _ hl0] using h1
      · simpa [div_mul_eq_mul_div] using hq2
      · simpa [div_mul_eq_mul_div] using hq3
  · -- version 3 ⇒ version 1, with `l₀ = x₀y₀`, `l₁ = x₁y₀`, `l₂ = x₀y₁`, `l₃ = x₀y₂`
    intro V3 x y hx hy hall
    have hx0 : x 0 ≠ 0 := hx.ne_zero 0
    have hy0 : y 0 ≠ 0 := hy.ne_zero 0
    refine V3 (x 0 * y 0) (x 1 * y 0) (x 0 * y 1) (x 0 * y 2) (hall 0 0) (hall 1 0) (hall 0 1)
      (hall 0 2) ?_ ?_ ⟨?_, ?_⟩
    · -- `a l₀ + b l₁ = y₀ (a x₀ + b x₁)`
      intro a b ha hb h
      refine indep_two hx ha hb ((mul_eq_zero.1 ?_).resolve_left hy0)
      linear_combination h
    · -- `a l₀ + b l₂ + c l₃ = x₀ (a y₀ + b y₁ + c y₂)`
      intro a b c ha hb hc h
      refine indep_three hy ha hb hc ((mul_eq_zero.1 ?_).resolve_left hx0)
      linear_combination h
    · have e : x 1 * y 0 * (x 0 * y 1) / (x 0 * y 0) = x 1 * y 1 := by
        field_simp
      rw [e]
      exact hall 1 1
    · have e : x 1 * y 0 * (x 0 * y 2) / (x 0 * y 0) = x 1 * y 2 := by
        field_simp
      rw [e]
      exact hall 1 2
