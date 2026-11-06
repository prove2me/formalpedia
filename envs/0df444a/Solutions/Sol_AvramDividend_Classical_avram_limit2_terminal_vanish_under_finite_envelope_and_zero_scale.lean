-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_terminal_vanish_under_finite_envelope_and_zero_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:18:00.468921+00:00
-- url     : https://prove2.me/submissions/8625243a-9ccf-4e6f-82a2-266ba33bfa70

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_lintegral_vanish_of_scaled_envelope
import Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_envelope_zero_scale_product_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Envelope : Ω → ℝ≥0∞)
    (hEnvelope : Measurable Envelope)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Envelope ω)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (hScale : Filter.Tendsto scale Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  exact AvramDividend.Classical.avram_limit2_terminal_lintegral_vanish_of_scaled_envelope
    P scale Envelope hEnvelope Terminal hBound
    (AvramDividend.Classical.avram_limit2_finite_envelope_zero_scale_product_vanish
      P scale Envelope hFinite hScale)
