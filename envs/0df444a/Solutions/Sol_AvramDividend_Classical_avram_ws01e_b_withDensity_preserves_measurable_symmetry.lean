-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_withDensity_preserves_measurable_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:44:27.173202+00:00
-- url     : https://prove2.me/submissions/474bcc1f-9caa-4c0c-b50b-2f875c054b07

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A density depending only on a symmetry-invariant statistic preserves
the base law's exact event symmetry under the same measurable map. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (R : α → α) (hR : Measurable R)
    (hSym : Measure.map R μ = μ)
    (w : α → ℝ≥0∞) (hw : Measurable w)
    (hwR : ∀ x, w (R x) = w x)
    (A : Set α) (hA : MeasurableSet A) :
    (μ.withDensity w) (R ⁻¹' A) = (μ.withDensity w) A := by
  have hPre : MeasurableSet (R ⁻¹' A) := hA.preimage hR
  have hAW : Measurable (A.indicator w) := hw.indicator hA
  rw [withDensity_apply w hPre, withDensity_apply w hA]
  rw [← lintegral_indicator hPre w, ← lintegral_indicator hA w]
  calc
    (∫⁻ x, (R ⁻¹' A).indicator w x ∂μ) =
      ∫⁻ x, (A.indicator w) (R x) ∂μ := by
        apply lintegral_congr
        intro x
        by_cases hx : R x ∈ A
        · simp [Set.indicator_of_mem, hx, hwR x]
        · simp [Set.indicator_of_notMem, hx]
    _ = ∫⁻ y, A.indicator w y ∂(Measure.map R μ) :=
      (lintegral_map hAW hR).symm
    _ = ∫⁻ y, A.indicator w y ∂μ := by rw [hSym]
