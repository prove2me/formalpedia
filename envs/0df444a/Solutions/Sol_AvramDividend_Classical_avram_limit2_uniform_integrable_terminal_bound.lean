-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_integrable_terminal_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:13:51.489549+00:00
-- url     : https://prove2.me/submissions/abddf931-1aa0-48cb-8fb5-b3891698ffd9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-! Remote CE repair: measurable factor and gcongr for ENNReal monotonicity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M) :
    ∀ n, (∫⁻ ω, Terminal n ω ∂P) ≤ scale n * M := by
  intro n
  calc
    _ ≤ ∫⁻ ω, scale n * Payoff n ω ∂P := lintegral_mono (hBound n)
    _ = scale n * (∫⁻ ω, Payoff n ω ∂P) := by
      rw [lintegral_const_mul _ (hPayoff n)]
    _ ≤ scale n * M := by
      gcongr <;> exact hUniform n
