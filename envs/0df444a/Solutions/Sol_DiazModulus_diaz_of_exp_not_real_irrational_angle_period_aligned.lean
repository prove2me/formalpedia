-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T14:25:08.110096+00:00
-- url     : https://prove2.me/submissions/604912e1-6870-461b-82e5-d58e1559c549
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      Transcendental ℚ (Complex.exp u) := by
  intro u h0 hmod hnr hax hirr hal
  by_cases h : ∃ r : ℚ, r ≠ 0 ∧
      IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
      ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))
  · exact DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
      u h0 hmod hnr hax hirr hal h
  · exact DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free
      u h0 hmod hnr hax hirr hal h
