-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_terminal_lintegral_vanish_of_scaled_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:14:41.478438+00:00
-- url     : https://prove2.me/submissions/459c779f-c341-4afb-b3b4-c92831e6242d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_lintegral_envelope_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (scale : ℕ → ℝ≥0∞)
    (Envelope : Ω → ℝ≥0∞)
    (hEnvelope : Measurable Envelope)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Envelope ω)
    (hDecay : Filter.Tendsto
      (fun n : ℕ => scale n * (∫⁻ ω, Envelope ω ∂P))
      Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hUpper n :=
    AvramDividend.Classical.avram_limit2_terminal_lintegral_envelope_bound
      P scale Envelope hEnvelope Terminal hBound n
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (0 : ℝ≥0∞)) Filter.atTop (nhds 0))
    hDecay (fun _ => bot_le) hUpper
