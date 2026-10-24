-- Prove2me | solution 1 for AvramDividend.Classical.integrable_causal_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:21:06.710317+00:00
-- url     : https://prove2.me/submissions/ca4296ab-836b-4e54-bfcc-e232b6b03d5f

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ContinuousLinearMap
open scoped Convolution

/-- The convolution of two real Lebesgue-integrable kernels is integrable. -/
theorem solution
    (f g : ℝ → ℝ) (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) volume := by
  change Integrable (f ⋆[mul ℝ ℝ, volume] g) volume
  exact hf.integrable_convolution (mul ℝ ℝ) hg
