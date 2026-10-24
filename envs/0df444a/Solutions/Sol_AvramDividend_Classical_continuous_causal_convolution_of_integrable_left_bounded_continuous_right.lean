-- Prove2me | solution 1 for AvramDividend.Classical.continuous_causal_convolution_of_integrable_left_bounded_continuous_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:36:10.246989+00:00
-- url     : https://prove2.me/submissions/d6f8034a-1589-4524-bae2-42b29f1db362

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ContinuousLinearMap
open scoped Convolution

/-- An L1 left factor convoluted with a bounded continuous right factor is continuous. -/
theorem solution
    (f g : ℝ → ℝ) (hfi : Integrable f volume)
    (hgb : BddAbove (Set.range fun x : ℝ => ‖g x‖))
    (hgc : Continuous g) :
    Continuous (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) := by
  change Continuous (f ⋆[mul ℝ ℝ, volume] g)
  exact hgb.continuous_convolution_right_of_integrable (mul ℝ ℝ) hfi hgc
