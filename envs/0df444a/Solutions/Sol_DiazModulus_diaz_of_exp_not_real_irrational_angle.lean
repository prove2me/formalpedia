-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_irrational_angle
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T10:40:24.938843+00:00
-- url     : https://prove2.me/submissions/e876b4ed-fd01-4a07-9d37-82a86d19f3f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_free

open Complex ComplexConjugate

-- The two children's extra hypotheses are literally complementary, so the reduction is a
-- `by_cases` on the split predicate and carries no mathematical content.
open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      Transcendental ℚ (Complex.exp u) := by
  intro u hu0 hmod hnr hax hirr
  by_cases h : ∃ r : ℚ, r ≠ 0 ∧
      IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)
  · exact DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned
      u hu0 hmod hnr hax hirr h
  · exact DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free
      u hu0 hmod hnr hax hirr h
