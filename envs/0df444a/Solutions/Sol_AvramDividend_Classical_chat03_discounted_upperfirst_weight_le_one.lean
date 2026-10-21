-- Prove2me | solution 1 for AvramDividend.Classical.chat03_discounted_upperfirst_weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:23:14.732032+00:00
-- url     : https://prove2.me/submissions/cacc1321-3dd8-41ad-a6fa-08bc80c77262

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

/-!
The exact upper-first discounted reward is bounded by one for
nonnegative discount rates. Extended passage times may be infinite.
-/
theorem solution (q : ℝ) (hq : 0 ≤ q)
    (up down : ℝ≥0∞) :
    (if up < down then
       ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
     else 0) ≤ 1 := by
  split_ifs with h
  · apply ENNReal.ofReal_le_one.mpr
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hq ENNReal.toReal_nonneg)
  · exact zero_le
