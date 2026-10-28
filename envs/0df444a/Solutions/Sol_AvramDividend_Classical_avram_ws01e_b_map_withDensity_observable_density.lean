-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_map_withDensity_observable_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:01:47.579827+00:00
-- url     : https://prove2.me/submissions/ebc5d87e-4cad-4bc0-9929-544a7b8d13ce

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Pushing a law forward through F commutes with a density depending
only on the observed F-value. -/
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (F : α → β) (hF : Measurable F)
    (w : β → ℝ≥0∞) (hw : Measurable w) :
    Measure.map F (μ.withDensity (w ∘ F)) =
      (Measure.map F μ).withDensity w := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hF hs]
  rw [withDensity_apply (w ∘ F) (hs.preimage hF),
    withDensity_apply w hs]
  rw [← lintegral_indicator (hs.preimage hF) (w ∘ F),
    ← lintegral_indicator hs w]
  calc
    (∫⁻ x, (F ⁻¹' s).indicator (w ∘ F) x ∂μ) =
        ∫⁻ x, (s.indicator w) (F x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : F x ∈ s
      · simp [Set.indicator_of_mem, hx, Function.comp_def]
      · simp [Set.indicator_of_notMem, hx, Function.comp_def]
    _ = ∫⁻ y, s.indicator w y ∂(Measure.map F μ) :=
        (lintegral_map (hw.indicator hs) hF).symm
