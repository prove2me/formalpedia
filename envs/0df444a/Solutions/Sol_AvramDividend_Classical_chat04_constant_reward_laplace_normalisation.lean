-- Prove2me | solution 1 for AvramDividend.Classical.chat04_constant_reward_laplace_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:50:13.221079+00:00
-- url     : https://prove2.me/submissions/b023db35-b753-467f-952a-355c8b0935b7

import Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_exponential_halfline_integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The Laplace transform of a constant reward equals reward divided by rate. -/
theorem solution (p c : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * c) = c / p := by
  calc
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * c) =
        (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) • c) := by
          simp only [smul_eq_mul]
    _ = (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t))) • c := by
      rw [integral_smul_const]
    _ = c / p := by
      rw [chat04_positive_discount_exponential_halfline_integral p hp]
      simp only [smul_eq_mul]
      ring
