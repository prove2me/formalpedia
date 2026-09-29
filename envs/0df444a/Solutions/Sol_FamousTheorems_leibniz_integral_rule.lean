-- Prove2me | solution 1 for FamousTheorems.leibniz_integral_rule
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:09:29.366815+00:00
-- url     : https://prove2.me/submissions/188b628b-1bd8-40f5-aeee-fd518ba4e570

import Mathlib

theorem solution {α 𝕜 E H : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup H] [NormedSpace 𝕜 H] {F : H → α → E}
    {F' : H → α → H →L[𝕜] E} {x₀ : H} {bound : α → ℝ} {s : Set H} (hs : s ∈ nhds x₀)
    (hF_meas : ∀ᶠ x in nhds x₀, MeasureTheory.AEStronglyMeasurable (F x) μ) (hF_int : MeasureTheory.Integrable (F x₀) μ)
    (hF'_meas : MeasureTheory.AEStronglyMeasurable (F' x₀) μ) (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : MeasureTheory.Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (fun x => F x a) (F' x a) x) :
    HasFDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
