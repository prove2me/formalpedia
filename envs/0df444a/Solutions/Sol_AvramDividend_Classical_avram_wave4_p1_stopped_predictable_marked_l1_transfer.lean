-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_l1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:38:58.175908+00:00
-- url     : https://prove2.me/submissions/6e08de0f-409e-469e-bfae-b3d4ca3cf7f1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_marked_predictable_measure_unique
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal

theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    [IsFiniteMeasure M]
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × E) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] G)
    (hGi : Integrable G M) :
    let H : ((ℝ≥0 × Ω) × E) → ℝ :=
      fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0
    Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] H ∧
    Integrable H M ∧ Integrable H N ∧
      (∫ p, H p ∂M) = ∫ p, H p ∂N := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × E) := Prod.instMeasurableSpace
  let H : ((ℝ≥0 × Ω) × E) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0
  change Measurable H ∧ Integrable H M ∧ Integrable H N ∧
    (∫ p, H p ∂M) = ∫ p, H p ∂N
  have hSurv := AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyPredictable τ hτ
  change StronglyMeasurable[𝓕.predictable]
    (fun q : ℝ≥0 × Ω =>
      if (q.1 : ℝ≥0∞) ≤ τ q.2 then (1 : ℝ) else 0) at hSurv
  have hSurvM := hSurv.measurable
  have hRegion : MeasurableSet[𝓕.predictable]
      {q : ℝ≥0 × Ω | (q.1 : ℝ≥0∞) ≤ τ q.2} := by
    have heq : {q : ℝ≥0 × Ω | (q.1 : ℝ≥0∞) ≤ τ q.2} =
        (fun q : ℝ≥0 × Ω =>
          if (q.1 : ℝ≥0∞) ≤ τ q.2 then (1 : ℝ) else 0) ⁻¹' {1} := by
      ext q
      by_cases hq : (q.1 : ℝ≥0∞) ≤ τ q.2 <;> simp [hq]
    rw [heq]
    exact hSurvM (MeasurableSet.singleton 1)
  have hRegionMark : MeasurableSet
      {p : ((ℝ≥0 × Ω) × E) | (p.1.1 : ℝ≥0∞) ≤ τ p.1.2} := by
    have heq : {p : ((ℝ≥0 × Ω) × E) |
        (p.1.1 : ℝ≥0∞) ≤ τ p.1.2} =
        {q : ℝ≥0 × Ω | (q.1 : ℝ≥0∞) ≤ τ q.2} ×ˢ Set.univ := by
      ext ⟨q, z⟩
      simp [Set.mem_prod]
    rw [heq]
    exact hRegion.prod MeasurableSet.univ
  have hHm : Measurable H :=
    Measurable.ite hRegionMark hGm measurable_const
  have hHi : Integrable H M := by
    have hEqH : H =
        ({p : ((ℝ≥0 × Ω) × E) |
          (p.1.1 : ℝ≥0∞) ≤ τ p.1.2}.indicator G) := by
      funext p
      by_cases hp : (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 <;> simp [H, hp]
    rw [hEqH]
    exact hGi.indicator hRegionMark
  have hEq : M = N :=
    AvramDividend.Classical.avram_wave4_p1_finite_marked_predictable_measure_unique
      𝓕 M N hBot hFuture
  refine ⟨hHm, hHi, ?_, ?_⟩
  · rwa [← hEq]
  · rw [hEq]
