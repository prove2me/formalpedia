-- Prove2me | solution 1 for AvramDividend.Classical.exp_negative_quadratic_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:25:30.568574+00:00
-- url     : https://prove2.me/submissions/40140d8a-a907-458e-b742-767e452c2904

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (t : ℝ) (ht : t ≤ 0) :
    ‖Real.exp t - 1 - t‖ ≤ t ^ 2 := by
  by_cases hsmall : -1 ≤ t
  · have hnorm : ‖t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos ht]
      linarith
    have h := Real.norm_exp_sub_one_sub_id_le hnorm
    simpa [Real.norm_eq_abs, sq_abs] using h
  · have hlarge : t ≤ -1 := by linarith
    have hlow : 0 ≤ Real.exp t - 1 - t := by
      linarith [Real.add_one_le_exp t]
    have hhigh : Real.exp t ≤ 1 := by
      exact Real.exp_monotone ht |>.trans (by simp)
    rw [Real.norm_eq_abs, abs_of_nonneg hlow]
    nlinarith [mul_nonneg (by linarith : 0 ≤ -t)
      (by linarith : 0 ≤ -(t + 1))]
