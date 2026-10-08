-- Prove2me | solution 1 for AvramDividend.Classical.sFinite_of_positive_lintegrable_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:05:27.856186+00:00
-- url     : https://prove2.me/submissions/a071eeb5-5003-4eb8-b768-2259bbaa7cbf

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞)
    (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0)
    (hint : ∫⁻ x, f x ∂μ ≠ ∞) :
    SFinite μ := by
  letI : IsFiniteMeasure (μ.withDensity f) :=
    isFiniteMeasure_withDensity hint
  exact sFinite_of_absolutelyContinuous
    (withDensity_absolutelyContinuous' hf hpos)
