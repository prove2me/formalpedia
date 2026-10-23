-- Prove2me | solution 1 for AvramDividend.Classical.chat07_weighted_compensated_negative_jump_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:52:54.453199+00:00
-- url     : https://prove2.me/submissions/fc8229db-cffe-47e6-ac77-a51768dad1c2

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-! A compensated negative jump is dominated pointwise by the positive
scale decrement and its nonnegative first-derivative compensation. -/
theorem solution
    (W : ℝ → ℝ) (hW : Monotone W)
    (θ x r : ℝ) (hr : 0 ≤ r) :
    Real.exp (-(θ * x)) *
        |W (x - r) - W x + r * deriv W x| ≤
      Real.exp (-(θ * x)) *
        ((W x - W (x - r)) + r * deriv W x) := by
  have hstep : W (x - r) ≤ W x :=
    hW (sub_le_self x hr)
  have hderiv : 0 ≤ deriv W x := hW.deriv_nonneg
  have hdelta : 0 ≤ W x - W (x - r) :=
    sub_nonneg.mpr hstep
  have hcomp : 0 ≤ r * deriv W x :=
    mul_nonneg hr hderiv
  have habs :
      |W (x - r) - W x + r * deriv W x| ≤
      (W x - W (x - r)) + r * deriv W x := by
    calc
      |W (x - r) - W x + r * deriv W x| =
          |r * deriv W x - (W x - W (x - r))| := by
        congr 1
        ring
      _ ≤ |r * deriv W x| + |W x - W (x - r)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (r * deriv W x) 0 (W x - W (x - r)))
      _ = (W x - W (x - r)) + r * deriv W x := by
        rw [abs_of_nonneg hcomp, abs_of_nonneg hdelta]
        ring
  exact mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
