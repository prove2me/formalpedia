-- Prove2me | solution 1 for AvramDividend.Classical.realIndicator_pushforward_one_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:22:48.074423+00:00
-- url     : https://prove2.me/submissions/973a8880-e374-4548-aa47-a9f998684e7d

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The mass of one under an event-indicator law equals the original event mass. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A) :
    (Measure.map (Set.indicator A (fun _ : Ω => (1 : ℝ))) P)
      ({1} : Set ℝ) = P A := by
  have hH : Measurable (Set.indicator A (fun _ : Ω => (1 : ℝ))) :=
    measurable_const.indicator hA
  rw [Measure.map_apply hH (measurableSet_singleton (1 : ℝ))]
  congr 1
  ext ω
  by_cases hh : ω ∈ A
  · simp [Set.indicator, hh]
  · simp [Set.indicator, hh]