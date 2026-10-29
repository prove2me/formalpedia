-- Prove2me | solution 1 for AvramDividend.Classical.exp_clock_Iic_strictly_positive_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:37:28.680474+00:00
-- url     : https://prove2.me/submissions/2128310e-e70b-4f57-b129-58fb82297c10

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution
    (p T : ℝ) (hp : 0 < p) (hT : 0 < T) :
    0 < (expMeasure p) (Iic T) := by
  have := isProbabilityMeasure_expMeasure hp
  rw [← ofReal_cdf, cdf_expMeasure_eq hp, if_pos hT.le, ENNReal.ofReal_pos, sub_pos,
    Real.exp_lt_one_iff, neg_lt_zero]
  positivity
