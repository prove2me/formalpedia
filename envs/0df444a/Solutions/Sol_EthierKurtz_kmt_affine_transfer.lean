-- Prove2me | solution 1 for EthierKurtz.kmt_affine_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:14:43.493773+00:00
-- url     : https://prove2.me/submissions/1ff95bd8-ff5f-40ca-9793-b31be58d99d0

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
import Theorems.Thm_EthierKurtz_kmt_affine_standardize
import Theorems.Thm_EthierKurtz_kmt_affine_image_transfer

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open EthierKurtz

theorem solution
    (H : ∀ (ν : ProbabilityMeasure Real),
      (Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
        Integrable (fun x : Real => Real.exp (a * x)) (ν : Measure Real)) →
      MeasureTheory.integral (ν : Measure Real) (fun x : Real => x) = 0 →
      variance (fun x : Real => x) (ν : Measure Real) = 1 →
        kmtApproximation ν)
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
    kmtApproximation μ := by
  obtain ⟨ν, m, σ, hσ, hmap, hmean, hvariance, hexpν⟩ :=
    EthierKurtz.kmt_affine_standardize μ hexp
  have happrox : EthierKurtz.kmtApproximation ν := H ν hexpν hmean hvariance
  exact EthierKurtz.kmt_affine_image_transfer μ ν m σ hσ hmap hmean hvariance happrox
