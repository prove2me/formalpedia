-- Prove2me | solution 1 for AvramDividend.Classical.real_exponentially_weighted_convolution_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T15:05:24.832543+00:00
-- url     : https://prove2.me/submissions/d248f3a4-7ff6-4376-bd9a-f269078ff857

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : Integrable (fun t : ℝ => Real.exp (-θ * t) * f t) volume)
    (hg : Integrable (fun t : ℝ => Real.exp (-θ * t) * g t) volume) :
    (∫ x : ℝ, ∫ s : ℝ,
      (Real.exp (-θ * s) * f s) *
        (Real.exp (-θ * (x - s)) * g (x - s)) ∂volume ∂volume) =
      (∫ s : ℝ, Real.exp (-θ * s) * f s ∂volume) *
        (∫ t : ℝ, Real.exp (-θ * t) * g t ∂volume) := by
  let F : ℝ → ℝ := fun t => Real.exp (-θ * t) * f t
  let G : ℝ → ℝ := fun t => Real.exp (-θ * t) * g t
  have hFi : Integrable F volume := hf
  have hGi : Integrable G volume := hg
  calc
    (∫ x : ℝ, ∫ s : ℝ, F s * G (x - s) ∂volume ∂volume) =
        ∫ x : ℝ,
          convolution F G (ContinuousLinearMap.mul ℝ ℝ) volume x ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (convolution_mul (μ := volume) (f := F) (g := G) (x := x)).symm
    _ = (∫ s : ℝ, F s ∂volume) *
          (∫ t : ℝ, G t ∂volume) := by
      simpa using
        (integral_convolution (μ := volume) (ν := volume)
          (ContinuousLinearMap.mul ℝ ℝ) hFi hGi)
