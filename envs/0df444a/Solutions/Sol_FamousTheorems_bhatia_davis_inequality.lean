-- Prove2me | solution 1 for FamousTheorems.bhatia_davis_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:06:56.163296+00:00
-- url     : https://prove2.me/submissions/6068fa8e-aea5-40d3-94f2-7c05eaab9616

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    ProbabilityTheory.variance X μ ≤ (b - ∫ ω, X ω ∂μ) * (∫ ω, X ω ∂μ - a) :=
  ProbabilityTheory.variance_le_sub_mul_sub h hX
