-- Prove2me | solution 1 for AvramDividend.Classical.real_causal_convolution_comm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:33:17.866603+00:00
-- url     : https://prove2.me/submissions/0e2ac575-4a63-450e-8cf9-b6a1ddac1e4a

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ContinuousLinearMap
open scoped Convolution

/-- Real additive convolution is symmetric under Lebesgue measure. -/
theorem solution (f g : ℝ → ℝ) (x : ℝ) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) =
      ∫ y : ℝ, g y * f (x - y) ∂volume := by
  calc
    (∫ y : ℝ, f y * g (x - y) ∂volume) =
      convolution f g (mul ℝ ℝ) volume x :=
        (convolution_mul).symm
    _ = ∫ y : ℝ, f (x - y) * g y ∂volume :=
      convolution_mul_swap
    _ = ∫ y : ℝ, g y * f (x - y) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact mul_comm _ _
