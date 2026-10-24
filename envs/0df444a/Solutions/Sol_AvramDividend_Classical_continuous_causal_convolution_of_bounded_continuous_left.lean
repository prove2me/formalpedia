-- Prove2me | solution 1 for AvramDividend.Classical.continuous_causal_convolution_of_bounded_continuous_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:19:34.747861+00:00
-- url     : https://prove2.me/submissions/a57774ea-4626-4f3b-ad88-a971841c1dd6

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ContinuousLinearMap
open scoped Convolution

/-- A bounded continuous left factor regularises convolution with an L1 right factor. -/
theorem solution
    (f g : ℝ → ℝ) (hfc : Continuous f)
    (hfb : BddAbove (Set.range fun x : ℝ => ‖f x‖))
    (hgi : Integrable g volume) :
    Continuous (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) := by
  change Continuous (f ⋆[mul ℝ ℝ, volume] g)
  exact hfb.continuous_convolution_left_of_integrable (mul ℝ ℝ) hfc hgi
