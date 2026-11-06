-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_finite_stochastic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:20:55.57433+00:00
-- url     : https://prove2.me/submissions/cae6b6c9-0e3a-4d9f-8094-66a954808d45

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit2_discount_factor_tendsto_zero_positive_rate
import Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_vanish_under_finite_envelope_and_zero_scale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (hq : 0 < q)
    (Envelope : Ω → ℝ≥0∞) (hEnvelope : Measurable Envelope)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤
      ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))) * Envelope ω) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  exact AvramDividend.Classical.avram_limit2_terminal_vanish_under_finite_envelope_and_zero_scale
    P (fun n => ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))))
    Envelope hEnvelope Terminal hBound hFinite
    (AvramDividend.Classical.avram_limit2_discount_factor_tendsto_zero_positive_rate q hq)
