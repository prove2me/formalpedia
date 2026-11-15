-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_one_step_discounted_cash_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:25:10.573559+00:00
-- url     : https://prove2.me/submissions/3056d55a-108a-4448-ba1d-7e00dd131f0c

import Mathlib.Analysis.Complex.ExponentialBounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
theorem solution : (1 / 2 : ℝ) < 1 - Real.exp (-1) := by
  have h : Real.exp (-1) < (1 / 2 : ℝ) := Real.exp_neg_one_lt_half
  linarith
