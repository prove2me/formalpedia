-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_terminal_vanish_of_uniform_integrable_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:22:08.009723+00:00
-- url     : https://prove2.me/submissions/f5d0706d-1805-4a6a-bb26-b28f4be98cde

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_integrable_terminal_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-! Repair: simplify the ENNReal limit 0 * M to 0 explicitly. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤)
    (hScale : Filter.Tendsto scale Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hUpper :=
    AvramDividend.Classical.avram_limit2_uniform_integrable_terminal_bound
      P scale Payoff Terminal hPayoff hBound M hUniform
  have hScaled :
      Filter.Tendsto (fun n => scale n * M)
        Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const hScale (Or.inr hFinite))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (0 : ℝ≥0∞)) Filter.atTop (nhds 0))
    hScaled (fun _ => bot_le) hUpper
