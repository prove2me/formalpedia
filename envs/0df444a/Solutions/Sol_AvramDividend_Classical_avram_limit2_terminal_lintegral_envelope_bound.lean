-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_terminal_lintegral_envelope_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:11:55.484839+00:00
-- url     : https://prove2.me/submissions/ec4b73d6-8064-4357-85d5-9fff67b0d5d0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-! Remote CE repair: lintegral_const_mul requires Measurable, not AEMeasurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (scale : ℕ → ℝ≥0∞)
    (Envelope : Ω → ℝ≥0∞)
    (hEnvelope : Measurable Envelope)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Envelope ω) :
    ∀ n, (∫⁻ ω, Terminal n ω ∂P) ≤
      scale n * (∫⁻ ω, Envelope ω ∂P) := by
  intro n
  calc
    _ ≤ ∫⁻ ω, scale n * Envelope ω ∂P := lintegral_mono (hBound n)
    _ = scale n * (∫⁻ ω, Envelope ω ∂P) := by
      rw [lintegral_const_mul _ hEnvelope]
