-- Prove2me | solution 1 for FamousTheorems.jensen_inequality_integral
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:40:24.668887+00:00
-- url     : https://prove2.me/submissions/1efce0c9-55ba-4d9a-ae94-8795a4282724

import Mathlib

theorem solution {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ] {s : Set E} {f : α → E} {g : E → ℝ}
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : MeasureTheory.Integrable f μ) (hgi : MeasureTheory.Integrable (g ∘ f) μ) :
    g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ :=
  hg.map_integral_le hgc hsc hfs hfi hgi
