-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_twist_Ioc_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:23:57.559979+00:00
-- url     : https://prove2.me/submissions/59f12868-dacd-41d8-9f0b-7e75234e966c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Exponential tilting distributes over both factors of a causal convolution. -/
theorem solution
    (k P : ℝ → ℝ) (w x : ℝ) :
    Real.exp (w * x) *
      (∫ s in Ioc (0 : ℝ) x, k s * P (x - s) ∂volume) =
    ∫ s in Ioc (0 : ℝ) x,
      (Real.exp (w * s) * k s) *
        (Real.exp (w * (x - s)) * P (x - s)) ∂volume := by
  calc
    _ = ∫ s in Ioc (0 : ℝ) x,
        Real.exp (w * x) * (k s * P (x - s)) ∂volume := by
          rw [integral_const_mul]
    _ = ∫ s in Ioc (0 : ℝ) x,
        (Real.exp (w * s) * k s) *
          (Real.exp (w * (x - s)) * P (x - s)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with s
          have he : Real.exp (w * x) =
              Real.exp (w * s) * Real.exp (w * (x - s)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [he]
          ring
