-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_unit_cash_interval_integral_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:28:36.50318+00:00
-- url     : https://prove2.me/submissions/7e0c4108-9154-449a-bb8d-43c015602596

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_one_step_discounted_cash_gt_half
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Real
theorem solution : (1 / 2 : ℝ) < ∫ x in (-1 : ℝ)..(0 : ℝ), Real.exp x := by
  rw [integral_exp]
  simpa only [Real.exp_zero] using
    AvramDividend.Classical.avram_bvb_obstruction_one_step_discounted_cash_gt_half
