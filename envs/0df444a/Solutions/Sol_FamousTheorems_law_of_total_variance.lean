-- Prove2me | solution 1 for FamousTheorems.law_of_total_variance
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:59:59.117192+00:00
-- url     : https://prove2.me/submissions/4ba03416-389b-4d15-8dca-27c6211473fd

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} {m₀ m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) :
    ∫ ω, condVar m X μ ω ∂μ + variance (μ[X | m]) μ = variance X μ :=
  integral_condVar_add_variance_condExp hm hX
