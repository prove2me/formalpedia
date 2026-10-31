-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyAdapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:29:21.431825+00:00
-- url     : https://prove2.me/submissions/ba21b281-2206-4f17-adb5-206f29b18f60

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal

/-- The inclusive survival indicator of a stopping time is strongly
adapted to the same filtration, even without path continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) := by
  intro t
  have hsurvive : MeasurableSet[𝓕 t]
      {ω : Ω | (t : ℝ≥0∞) ≤ τ ω} :=
    hτ.measurableSet_ge t
  exact (Measurable.ite hsurvive measurable_const measurable_const).stronglyMeasurable
