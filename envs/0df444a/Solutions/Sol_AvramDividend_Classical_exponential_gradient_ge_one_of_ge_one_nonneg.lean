-- Prove2me | solution 1 for AvramDividend.Classical.exponential_gradient_ge_one_of_ge_one_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:26:57.371506+00:00
-- url     : https://prove2.me/submissions/4bcaeec5-f30f-4dd6-bdb5-f869ddecb223

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    (θ x : ℝ) (hθ : 1 ≤ θ) (hx : 0 ≤ x) :
    1 ≤ deriv (fun y : ℝ => Real.exp (θ * y)) x := by
  have hd : deriv (fun y : ℝ => Real.exp (θ * y)) x =
      θ * Real.exp (θ * x) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 1 θ) x
    simpa using h
  rw [hd]
  have hθ0 : 0 ≤ θ := le_trans zero_le_one hθ
  have he : 1 ≤ Real.exp (θ * x) :=
    Real.one_le_exp (mul_nonneg hθ0 hx)
  have hmul : (1 : ℝ) * 1 ≤ θ * Real.exp (θ * x) :=
    mul_le_mul hθ he zero_le_one hθ0
  simpa only [one_mul] using hmul
