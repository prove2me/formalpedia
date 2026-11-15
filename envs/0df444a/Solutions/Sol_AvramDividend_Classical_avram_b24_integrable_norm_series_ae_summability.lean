-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_integrable_norm_series_ae_summability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:16:27.379648+00:00
-- url     : https://prove2.me/submissions/a39d7fe9-9caa-4969-b033-b573925424f3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_integrable_norm_series_integrable_total_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (H : ℕ → Ω → ℝ)
    (hHI : ∀ k, Integrable (H k) P)
    (hSum : Summable (fun k => ∫ ω, ‖H k ω‖ ∂P)) :
    ∃ (B : Ω → ℝ),
      Integrable B P ∧
      (∀ᵐ ω ∂P, Summable (fun k => ‖H k ω‖)) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖H k ω‖ ≤ B ω)  := by
  obtain ⟨B, hBI, hAE, hBound⟩ :=
    avram_b24_integrable_norm_series_integrable_total_envelope H hHI hSum
  refine ⟨B, hBI, ?_, hBound⟩
  filter_upwards [hAE] with ω hω
  exact hω.1
