-- Prove2me | solution 1 for EthierKurtz.kmt_affine_image_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:45:37.433865+00:00
-- url     : https://prove2.me/submissions/ae539883-ee89-4d9c-989a-b33785e62956

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
import Theorems.Thm_EthierKurtz_kmt_affine_image_pushforward

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem solution
    (μ ν : ProbabilityMeasure Real) (m σ : Real)
    (hσ : 0 ≤ σ)
    (hmap : Measure.map (fun y : Real => m + σ * y) (ν : Measure Real) = (μ : Measure Real))
    (hmean : MeasureTheory.integral (ν : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (ν : Measure Real) = 1)
    (happrox : EthierKurtz.kmtApproximation ν) :
    EthierKurtz.kmtApproximation μ := by
  exact EthierKurtz.kmt_affine_image_pushforward μ ν m σ hσ hmap hmean hvariance happrox
