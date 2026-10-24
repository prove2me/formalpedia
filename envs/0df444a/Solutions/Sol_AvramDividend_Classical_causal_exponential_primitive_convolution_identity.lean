-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_primitive_convolution_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:24:04.111019+00:00
-- url     : https://prove2.me/submissions/6cc70ba6-3a41-4351-aad5-a53f118a0e17

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Recast the exponentially untilted causal primitive as a convolution
with the nonnegative time-lag exponential damping factor. -/
theorem solution
    (P : ℝ → ℝ) (w x : ℝ) :
    Real.exp (-w * x) *
      (∫ s in (0 : ℝ)..x, Real.exp (w * s) * P s) =
    ∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s := by
  have hpoint (s : ℝ) :
      Real.exp (-w * x) * (Real.exp (w * s) * P s) =
        Real.exp (-w * (x - s)) * P s := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-w * x) *
        (∫ s in (0 : ℝ)..x, Real.exp (w * s) * P s) =
      ∫ s in (0 : ℝ)..x,
        Real.exp (-w * x) * (Real.exp (w * s) * P s) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in (0 : ℝ)..x,
          Real.exp (-w * (x - s)) * P s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hpoint s
