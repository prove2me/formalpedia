-- Prove2me | solution 1 for FamousTheorems.conditional_jensen_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:09:50.519872+00:00
-- url     : https://prove2.me/submissions/400945aa-e68d-4a43-8592-862a50cf4da7

import Mathlib

open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {α : Type*} {f : α → E} {φ : E → ℝ}
    {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E} (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ : ConvexOn ℝ s φ) (hφc : LowerSemicontinuousOn φ s) (hfs : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf : Integrable f μ) (hφf : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  ConvexOn.map_condExp_le hm hφ hφc hfs hs hf hφf
