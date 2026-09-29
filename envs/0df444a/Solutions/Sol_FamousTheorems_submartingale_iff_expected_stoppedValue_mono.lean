-- Prove2me | solution 1 for FamousTheorems.submartingale_iff_expected_stoppedValue_mono
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:45:36.875611+00:00
-- url     : https://prove2.me/submissions/a85adaf8-b857-441a-966b-47b0978e4685

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Real Topology ENNReal

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ σ : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 σ →
      τ ≤ σ → (∃ N : ℕ, ∀ x, σ x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f σ] :=
  MeasureTheory.submartingale_iff_expected_stoppedValue_mono hadp hint
