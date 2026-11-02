-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_predictable_sample_mark_lift_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:37:24.741177+00:00
-- url     : https://prove2.me/submissions/0b4ad995-9fa1-4357-819d-3ace1e5fab17

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_adapted_rectangle_sigma_generator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) := by
  let G : Set (Set (ℝ≥0 × Ω)) :=
    {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
      S = ({⊥} ×ˢ A)) ∨
      (∃ i : ℝ≥0, ∃ A : Set Ω,
        MeasurableSet[𝓕 i] A ∧ S = (Set.Ioi i ×ˢ A))}
  have hgen : 𝓕.predictable = MeasurableSpace.generateFrom G := by
    exact avram_wave4_p1_predictable_adapted_rectangle_sigma_generator 𝓕
  have hsection (S : Set ℝ≥0) (hS : MeasurableSet S)
      (A : Set Ω) :
      MeasurableSet ((fun t : ℝ≥0 => (t, ω)) ⁻¹' (S ×ˢ A)) := by
    by_cases hω : ω ∈ A
    · have heq :
          (fun t : ℝ≥0 => (t, ω)) ⁻¹' (S ×ˢ A) = S := by
        ext t
        simp [hω]
      rw [heq]
      exact hS
    · have heq :
          (fun t : ℝ≥0 => (t, ω)) ⁻¹' (S ×ˢ A) = ∅ := by
        ext t
        simp [hω]
      rw [heq]
      exact MeasurableSet.empty
  have htime : @Measurable ℝ≥0 (ℝ≥0 × Ω)
      (inferInstance : MeasurableSpace ℝ≥0)
      (𝓕.predictable) (fun t => (t, ω)) := by
    rw [hgen]
    apply measurable_generateFrom
    intro S hS
    rcases hS with ⟨A, _, rfl⟩ | ⟨i, A, _, rfl⟩
    · exact hsection {⊥} (measurableSet_singleton _) A
    · exact hsection (Set.Ioi i) measurableSet_Ioi A
  have hfst : @Measurable (ℝ≥0 × ℝ) (ℝ≥0 × Ω)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (𝓕.predictable) (fun p => (p.1, ω)) :=
    htime.comp measurable_fst
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact hfst.prodMk measurable_snd
