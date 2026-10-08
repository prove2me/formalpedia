-- Prove2me | solution 1 for AvramDividend.Classical.compensated_exponential_quadratic_of_small_argument
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:25:29.4509+00:00
-- url     : https://prove2.me/submissions/7bc634dd-866d-4b35-a368-f470e1071fa2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (θ y : ℝ) (hsmall : ‖θ * y‖ ≤ 1) :
    ‖Real.exp (θ * y) - 1 - θ * y‖ ≤ θ ^ 2 * y ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le hsmall
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h
