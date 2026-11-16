-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_discounted_cash_terminal_lower_gt_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:32:08.061224+00:00
-- url     : https://prove2.me/submissions/cde31da4-dcb1-4b1f-b170-1178847af8f4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
theorem solution :
    (1 / 2 : ℝ) <
      (1 / 10 + 1 / 2) * Real.exp (-(1 / 10 : ℝ)) := by
  have hExp : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 10 : ℝ))
    norm_num at h ⊢
    linarith
  nlinarith
