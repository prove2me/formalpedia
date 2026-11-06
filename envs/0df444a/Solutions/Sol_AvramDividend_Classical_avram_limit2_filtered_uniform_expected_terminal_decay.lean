-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_filtered_uniform_expected_terminal_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:24:59.503209+00:00
-- url     : https://prove2.me/submissions/2e03bafe-e2de-4efa-a955-08f7af50f1fd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-! Any filter of horizons, including real atTop or a cofinal stopped sequence. -/
theorem solution
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (l : Filter ι) (scale : ι → ℝ≥0∞)
    (Payoff Terminal : ι → Ω → ℝ≥0∞)
    (hPayoff : ∀ i, Measurable (Payoff i))
    (hBound : ∀ i ω, Terminal i ω ≤ scale i * Payoff i ω)
    (M : ℝ≥0∞) (hUniform : ∀ i, (∫⁻ ω, Payoff i ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤)
    (hScale : Filter.Tendsto scale l (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun i => ∫⁻ ω, Terminal i ω ∂P)
      l (nhds (0 : ℝ≥0∞)) := by
  have hUpper i : (∫⁻ ω, Terminal i ω ∂P) ≤ scale i * M := by
    calc
      _ ≤ ∫⁻ ω, scale i * Payoff i ω ∂P := lintegral_mono (hBound i)
      _ = scale i * (∫⁻ ω, Payoff i ω ∂P) := by
        rw [lintegral_const_mul _ (hPayoff i)]
      _ ≤ scale i * M := by
        gcongr <;> exact hUniform i
  have hScaled : Filter.Tendsto (fun i => scale i * M)
      l (nhds (0 : ℝ≥0∞)) := by
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const hScale (Or.inr hFinite))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0))
    hScaled (fun _ => bot_le) hUpper
