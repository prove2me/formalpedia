-- Prove2me | solution 1 for DiazModulus.diaz_2007_cor4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:10:20.187696+00:00
-- url     : https://prove2.me/submissions/e42a45b6-1d47-41d4-91e9-b1a4df0b95c1

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_quadratic_eq_zero_of_not_mem_Qbar

/-!
# Diaz 2007, Corollaire 4

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres
algébriques*, JTNB 19 (2007), Corollaire 4, p. 383, with the proof on pp. 383–384.

`hSSE` is the strong six exponentials hypothesis, version 1: for `Q̄`-linearly independent
`x : Fin 2 → ℂ` and `y : Fin 3 → ℂ`, not every product `x i * y j` lies in `ℒ̃`.

* **1)** Apply `hSSE` to `x = (l₁, l₂)` and `y = (1, l₃/l₁, l₄/l₂)`. The six products are
  `l₁, l₃, l₄ l₁/l₂, l₂, l₃ l₂/l₁, l₄`. A relation `g₀ + g₁ l₃/l₁ + g₂ l₄/l₂ = 0`, times
  `l₁ l₂`, is the relation `g₀ (l₁ l₂) + g₂ (l₁ l₄) + g₁ (l₂ l₃) = 0`.
* **2)** Part 1 with `l₃ = l₄ = 1`.
* **3)** Part 1 with `l₃ = l₂` and `l₄ = l₁`. The triple `(l₁ l₂, l₁², l₂²)` is free: divided
  by `l₂²`, a relation is a quadratic equation in `t = l₁/l₂`, and `t ∉ Q̄` because `(l₁, l₂)`
  is free.
* **4)** Part 1 with `l₂ = conj l₁` and `l₄ = conj l₃`, which lie in `ℒ̃` by conjugation
  stability. The two quotients of part 1 are then conjugate to each other.
-/

open Complex ComplexConjugate

namespace D5_diaz_2007_cor4

open DiazModulus

/-- `1 ∈ ℒ̃`. -/
theorem one_mem_logAlgTilde : (1 : ℂ) ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

end D5_diaz_2007_cor4

open DiazModulus D5_diaz_2007_cor4 in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ l₁ l₂ l₃ l₄ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde →
      l₄ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
        a * (l₁ * l₂) + b * (l₁ * l₄) + c * (l₂ * l₃) = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * l₂ = 0 → a = 0 ∧ b = 0) →
      ¬ (l₄ * l₁ / l₂ ∈ LogAlgTilde ∧ l₃ * l₂ / l₁ ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₁ + b * l₂ + c * (l₁ * l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ / l₂ ∈ LogAlgTilde ∧ l₂ / l₁ ∈ LogAlgTilde)) ∧
    -- 3)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * l₂ = 0 → a = 0 ∧ b = 0) →
      ¬ (l₁ ^ 2 / l₂ ∈ LogAlgTilde ∧ l₂ ^ 2 / l₁ ∈ LogAlgTilde)) ∧
    -- 4)
    (∀ l₁ l₃ : ℂ, l₁ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * conj l₁ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
        a * (l₁ * conj l₁) + b * (l₁ * conj l₃) + c * (conj l₁ * l₃) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l₁ * conj l₃ / conj l₁ ∉ LogAlgTilde) := by
  -- 1) `hSSE` on `x = (l₁, l₂)`, `y = (1, l₃/l₁, l₄/l₂)`
  have part1 : ∀ l₁ l₂ l₃ l₄ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde →
      l₄ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
        a * (l₁ * l₂) + b * (l₁ * l₄) + c * (l₂ * l₃) = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * l₂ = 0 → a = 0 ∧ b = 0) →
      ¬ (l₄ * l₁ / l₂ ∈ LogAlgTilde ∧ l₃ * l₂ / l₁ ∈ LogAlgTilde) := by
    intro l₁ l₂ l₃ l₄ h₁ h₂ h₃ h₄ hfree3 hfree2 ⟨h41, h32⟩
    have hl₁ : l₁ ≠ 0 := fun h0 =>
      one_ne_zero (hfree2 1 0 Qbar.one_mem Qbar.zero_mem (by rw [h0]; ring)).1
    have hl₂ : l₂ ≠ 0 := fun h0 =>
      one_ne_zero (hfree2 0 1 Qbar.zero_mem Qbar.one_mem (by rw [h0]; ring)).2
    refine hSSE ![l₁, l₂] ![1, l₃ / l₁, l₄ / l₂] ?_ ?_ ?_
    · -- `(l₁, l₂)` is free
      rw [LinearIndependent.pair_iff]
      intro s t hst
      obtain ⟨hs, ht⟩ := hfree2 s t s.2 t.2 hst
      exact ⟨Subtype.ext hs, Subtype.ext ht⟩
    · -- `(1, l₃/l₁, l₄/l₂)` is free: clear denominators, note the order `g₀, g₂, g₁`
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      have hg' : (g 0 : ℂ) * 1 + (g 1 : ℂ) * (l₃ / l₁) + (g 2 : ℂ) * (l₄ / l₂) = 0 := hg
      have e : (g 0 : ℂ) * (l₁ * l₂) + (g 2 : ℂ) * (l₁ * l₄) + (g 1 : ℂ) * (l₂ * l₃)
          = (l₁ * l₂) * ((g 0 : ℂ) * 1 + (g 1 : ℂ) * (l₃ / l₁) + (g 2 : ℂ) * (l₄ / l₂)) := by
        field_simp
        ring
      obtain ⟨h0, h2, h1⟩ :=
        hfree3 _ _ _ (g 0).2 (g 2).2 (g 1).2 (by rw [e, hg', mul_zero])
      intro i
      fin_cases i
      exacts [Subtype.ext h0, Subtype.ext h1, Subtype.ext h2]
    · -- the six products
      have e₁ : l₁ * (l₃ / l₁) = l₃ := by field_simp
      have e₂ : l₁ * (l₄ / l₂) = l₄ * l₁ / l₂ := by ring
      have e₃ : l₂ * (l₃ / l₁) = l₃ * l₂ / l₁ := by ring
      have e₄ : l₂ * (l₄ / l₂) = l₄ := by field_simp
      intro i j
      fin_cases i <;> fin_cases j <;> simp
      · exact h₁
      · rwa [e₁]
      · rwa [e₂]
      · exact h₂
      · rwa [e₃]
      · rwa [e₄]
  refine ⟨part1, ?_, ?_, ?_⟩
  · -- 2) part 1 with `l₃ = l₄ = 1`
    intro l₁ l₂ h₁ h₂ hfree h
    refine part1 l₁ l₂ 1 1 h₁ h₂ one_mem_logAlgTilde one_mem_logAlgTilde ?_ ?_
      (by simpa only [one_mul] using h)
    · intro a b c ha hb hc habc
      obtain ⟨hb', hc', ha'⟩ := hfree b c a hb hc ha (by linear_combination habc)
      exact ⟨ha', hb', hc'⟩
    · intro a b ha hb hab
      obtain ⟨ha', hb', -⟩ := hfree a b 0 ha hb Qbar.zero_mem (by linear_combination hab)
      exact ⟨ha', hb'⟩
  · -- 3) part 1 with `l₃ = l₂`, `l₄ = l₁`; a relation is a quadratic equation in `l₁/l₂`
    intro l₁ l₂ h₁ h₂ hfree h
    have hl₂ : l₂ ≠ 0 := fun h0 =>
      one_ne_zero (hfree 0 1 Qbar.zero_mem Qbar.one_mem (by rw [h0]; ring)).2
    have ht : l₁ / l₂ ∉ Qbar := fun ht =>
      one_ne_zero (hfree 1 (-(l₁ / l₂)) Qbar.one_mem (Qbar.neg_mem ht) (by field_simp; ring)).1
    refine part1 l₁ l₂ l₂ l₁ h₁ h₂ h₂ h₁ ?_ hfree (by simpa only [sq] using h)
    intro a b c ha hb hc habc
    have e : b * (l₁ / l₂) ^ 2 + a * (l₁ / l₂) + c
        = (a * (l₁ * l₂) + b * (l₁ * l₁) + c * (l₂ * l₂)) / l₂ ^ 2 := by
      field_simp
      ring
    rw [habc, zero_div] at e
    obtain ⟨hb', ha', hc'⟩ := quadratic_eq_zero_of_not_mem_Qbar ht hb ha hc e
    exact ⟨ha', hb', hc'⟩
  · -- 4) part 1 with `l₂ = conj l₁`, `l₄ = conj l₃`; the two quotients are conjugate
    intro l₁ l₃ h₁ h₃ hfree2 hfree3 h
    have hc := logAlgTilde_conj_stable _ h
    rw [map_div₀, map_mul, conj_conj, conj_conj] at hc
    exact part1 l₁ (conj l₁) l₃ (conj l₃) h₁ (logAlgTilde_conj_stable _ h₁) h₃
      (logAlgTilde_conj_stable _ h₃) hfree3 hfree2 ⟨by rwa [mul_comm], by rwa [mul_comm]⟩
