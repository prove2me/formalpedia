-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_compensated_jump_pos_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T23:07:59.19766+00:00
-- url     : https://prove2.me/submissions/f5e13eae-c4c7-47d6-91e8-e9c848a94f04

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The compensated negative-jump exponential is nonnegative and at most its linear term. -/
theorem solution
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    0 ≤ Real.exp (-θ * z) - 1 + θ * z ∧
      Real.exp (-θ * z) - 1 + θ * z ≤ θ * z := by
  have hprod : 0 ≤ θ * z := mul_nonneg hθ hz
  have hlo := Real.add_one_le_exp (-θ * z)
  have hhi : Real.exp (-θ * z) ≤ 1 := by
    have h : -θ * z ≤ 0 := by nlinarith
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr h)
  constructor <;> nlinarith
