-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_deriv_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:47:55.618081+00:00
-- url     : https://prove2.me/submissions/41b78a97-3efd-46d9-9b15-ae3a53458d25

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal

/-- Composing a strongly predictable real process with the real derivative
of an arbitrary function preserves strong predictability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (w : ℝ → ℝ) :
    IsStronglyPredictable 𝓕 (fun t ω => deriv w (Z t ω)) := by
  change StronglyMeasurable[𝓕.predictable]
    (fun p : ℝ≥0 × Ω => deriv w (Z p.1 p.2))
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact ((measurable_deriv w).comp hZ.measurable).stronglyMeasurable
