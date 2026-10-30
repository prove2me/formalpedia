-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_drifted_natural_filtration_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:51:06.984218+00:00
-- url     : https://prove2.me/submissions/6a76e707-d22b-4fda-9124-c38b987ccf17

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A deterministic drift does not add information to the natural filtration. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0,
      StronglyMeasurable (fun ω => U t ω - (t : ℝ)))
    (s : ℝ≥0) :
    (Filtration.natural
        (fun t ω => U t ω - (t : ℝ)) hmeas) s ≤
      MeasurableSpace.comap
        (fun ω (u : Set.Iic s) => U (u : ℝ≥0) ω) inferInstance := by
  rw [Filtration.natural_eq_comap]
  let g : (Set.Iic s → ℝ) → (Set.Iic s → ℝ) :=
    fun p u => p u - ((u : ℝ≥0) : ℝ)
  have hg : Measurable g := by
    exact measurable_pi_iff.mpr (fun u =>
      (measurable_pi_apply u).sub_const _)
  have hf :
      (fun ω (u : Set.Iic s) =>
        U (u : ℝ≥0) ω - ((u : ℝ≥0) : ℝ)) =
      g ∘ (fun ω (u : Set.Iic s) => U (u : ℝ≥0) ω) := by
    rfl
  rw [hf]
  simpa only [MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono hg.comap_le :
      MeasurableSpace.comap
        (fun ω (u : Set.Iic s) => U (u : ℝ≥0) ω)
        (MeasurableSpace.comap g inferInstance) ≤
      MeasurableSpace.comap
        (fun ω (u : Set.Iic s) => U (u : ℝ≥0) ω)
        inferInstance)
