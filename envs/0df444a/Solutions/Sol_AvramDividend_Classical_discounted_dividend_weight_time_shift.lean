-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_weight_time_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:50:47.661976+00:00
-- url     : https://prove2.me/submissions/75e4c784-bc8a-42f4-a1ee-53692252f461

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (q : ℝ) (u t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * ((u + t : ℝ≥0) : ℝ)))) =
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) := by
  have hsum : -(q * ((u + t : ℝ≥0) : ℝ)) =
      -(q * (u : ℝ)) + -(q * (t : ℝ)) := by
    push_cast
    ring
  rw [hsum, Real.exp_add]
  exact ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))
