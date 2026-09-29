-- Prove2me | solution 1 for FamousTheorems.independent_expectation_product_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:45:27.049959+00:00
-- url     : https://prove2.me/submissions/96ccc316-8152-4887-87f8-ef91035cf2fe

import Mathlib

open MeasureTheory

theorem solution {Ω 𝕜 : Type*} [RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → 𝕜}
    (hXY : ProbabilityTheory.IndepFun X Y μ) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ :=
  hXY.integral_mul_eq_mul_integral hX hY
