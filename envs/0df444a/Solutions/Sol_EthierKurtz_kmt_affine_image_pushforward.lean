-- Prove2me | solution 1 for EthierKurtz.kmt_affine_image_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T21:02:28.053369+00:00
-- url     : https://prove2.me/submissions/9a63f5fb-29d1-4f95-ab48-27d49861bbcd

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
import Theorems.Thm_EthierKurtz_kmt_affine_image_moments
import Theorems.Thm_EthierKurtz_kmt_affine_image_transport_of_moments

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem solution
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hsig : 0 <= sig)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1)
    (happrox : EthierKurtz.kmtApproximation nu) :
    EthierKurtz.kmtApproximation mu := by
  obtain ⟨hmu_mean, hmu_variance⟩ :=
    EthierKurtz.kmt_affine_image_moments mu nu m sig hmap hmean hvariance
  exact EthierKurtz.kmt_affine_image_transport_of_moments
    mu nu m sig hsig hmap hmean hvariance hmu_mean hmu_variance happrox
