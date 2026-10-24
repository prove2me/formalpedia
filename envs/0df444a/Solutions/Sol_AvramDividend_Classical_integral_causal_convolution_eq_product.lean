-- Prove2me | solution 1 for AvramDividend.Classical.integral_causal_convolution_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:21:12.578948+00:00
-- url     : https://prove2.me/submissions/2fd79b94-ce1d-443d-8ab3-926385fe61c8

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ContinuousLinearMap
open scoped Convolution

/-- Real L1 convolution total mass is the product of the two L1 masses. -/
theorem solution
    (f g : ℝ → ℝ) (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x : ℝ, (∫ y : ℝ, f y * g (x - y) ∂volume) ∂volume) =
      (∫ x : ℝ, f x ∂volume) * (∫ x : ℝ, g x ∂volume) := by
  change (∫ x : ℝ, (f ⋆[mul ℝ ℝ, volume] g) x ∂volume) =
    (mul ℝ ℝ) (∫ x : ℝ, f x ∂volume) (∫ x : ℝ, g x ∂volume)
  exact MeasureTheory.integral_convolution (mul ℝ ℝ) hf hg
