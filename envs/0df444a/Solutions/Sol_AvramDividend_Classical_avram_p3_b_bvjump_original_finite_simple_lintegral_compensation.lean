-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_finite_simple_lintegral_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:40:21.956901+00:00
-- url     : https://prove2.me/submissions/afa3399c-8ae6-4a7b-a901-ba74a0c0c5fb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (A : ℕ → Set Ω) (B : ℕ → Set ℝ)
    (c : ℕ → ℝ≥0∞)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    (∫⁻ p, ∑ i ∈ S,
      (((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i).indicator
        (fun _ => c i)) p ∂M) =
    (∫⁻ p, ∑ i ∈ S,
      (((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i).indicator
        (fun _ => c i)) p ∂N) := by
  classical
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    @Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)
  let E : ℕ → Set ((ℝ≥0 × Ω) × ℝ) :=
    fun i => ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)
  have hEm : ∀ i ∈ S, MeasurableSet[
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (E i) := by
    intro i hi
    exact avram_p3_b_bvjump_original_predictable_finite_cell_measurable
      𝓕 (s i) (t i) (A i) (hA i hi) (B i) (hB i hi)
  have hFi : ∀ i ∈ S,
      Measurable (fun p => (E i).indicator (fun _ => c i) p) := by
    intro i hi
    exact measurable_const.indicator (hEm i hi)
  have hMass : ∀ i ∈ S, M (E i) = N (E i) := by
    intro i hi
    exact hRect (s i) (t i) (hst i hi) (A i) (hA i hi)
      (B i) (hB i hi)
  change (∫⁻ p, ∑ i ∈ S, (E i).indicator (fun _ => c i) p ∂M) =
      (∫⁻ p, ∑ i ∈ S, (E i).indicator (fun _ => c i) p ∂N)
  calc
    (∫⁻ p, ∑ i ∈ S, (E i).indicator (fun _ => c i) p ∂M) =
        ∑ i ∈ S, c i * M (E i) := by
      rw [lintegral_finsetSum S hFi]
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_indicator_const (hEm i hi) (c i)
    _ = ∑ i ∈ S, c i * N (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hMass i hi]
    _ = (∫⁻ p, ∑ i ∈ S, (E i).indicator (fun _ => c i) p ∂N) := by
      rw [lintegral_finsetSum S hFi]
      apply Finset.sum_congr rfl
      intro i hi
      exact (lintegral_indicator_const (hEm i hi) (c i)).symm
