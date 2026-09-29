-- Prove2me | solution 2 for DiazModulus.aligned_norm_free_no_rational_log_matrix
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:17.261756+00:00
-- url     : https://prove2.me/submissions/fcbba6fb-f635-4e2f-b2e3-f9e298d9feed

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_aligned_norm_free_no_quadratic_relation
import Theorems.Thm_DiazModulus_four_exp_barrier_of_no_quadratic_relation

open Complex ComplexConjugate

/- Write each entry as a rational linear form in `u, ū, 2πi`. These numbers satisfy no rational
quadratic relation (`aligned_norm_free_no_quadratic_relation`), so
`four_exp_barrier_of_no_quadratic_relation` gives the row or column relation. -/
open DiazModulus in
theorem solution :
    ∀ (u : ℂ) (r : ℚ),
      Transcendental ℚ ((Real.pi : ℝ) : ℂ) →
      u.re ≠ 0 →
      Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0 →
      IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) →
      IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ) →
      (¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      ∀ l : Fin 2 → Fin 2 → ℂ,
        (∀ i j, ∃ a b c : ℚ, l i j = (a : ℂ) * u + (b : ℂ) * (starRingEnd ℂ) u
          + (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) →
        l 0 0 * l 1 1 - l 0 1 * l 1 0 = 0 →
        (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a : ℂ) * l 0 0 + (b : ℂ) * l 1 0 = 0 ∧
            (a : ℂ) * l 0 1 + (b : ℂ) * l 1 1 = 0)
      ∨ (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a : ℂ) * l 0 0 + (b : ℂ) * l 0 1 = 0 ∧
            (a : ℂ) * l 1 0 + (b : ℂ) * l 1 1 = 0) := by
  intro u r _ hre hβ0 hβ hρ hfree l hl hdet
  choose a b c habc using hl
  have hM : ∀ i j, l i j = ∑ k, ((![a i j, b i j, c i j] k : ℚ) : ℂ) *
      ![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] k := by
    intro i j
    rw [habc i j, Fin.sum_univ_three]
    simp
  rcases four_exp_barrier_of_no_quadratic_relation _
      (fun F hF => aligned_norm_free_no_quadratic_relation u r hre hβ0 hβ hρ hfree F hF)
      (fun i j => ![a i j, b i j, c i j]) l hM (by linear_combination hdet) with
    ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩
  · exact Or.inl ⟨p, q, not_and_or.mp hpq, h 0, h 1⟩
  · exact Or.inr ⟨p, q, not_and_or.mp hpq, h 0, h 1⟩

#print axioms solution
