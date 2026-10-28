-- Prove2me | solution 1 for AvramDividend.Classical.indicator_indepFun_of_both_event_marginals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:07:20.734512+00:00
-- url     : https://prove2.me/submissions/a8ab4239-ea38-4fe3-b7c3-c3caa852cbee

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set

/-- Factoring the A and Aᶜ marginals makes the event indicator independent. -/
theorem solution

    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (Y : Ω → β)
    (hA : MeasurableSet A) (hY : Measurable Y)
    (hFirst : ∀ B : Set β, MeasurableSet B →
      P (A ∩ Y ⁻¹' B) = P A * P (Y ⁻¹' B))
    (hSecond : ∀ B : Set β, MeasurableSet B →
      P (Aᶜ ∩ Y ⁻¹' B) = P Aᶜ * P (Y ⁻¹' B)) :
    IndepFun (Set.indicator A (fun _ : Ω => (1 : ℝ))) Y P := by
  classical
  apply (indepFun_iff_measure_inter_preimage_eq_mul).2
  intro s B hs hB
  by_cases hs1 : (1 : ℝ) ∈ s
  · by_cases hs0 : (0 : ℝ) ∈ s
    · have hpre :
          (Set.indicator A (fun _ : Ω => (1 : ℝ))) ⁻¹' s = Set.univ := by
        ext ω
        by_cases hω : ω ∈ A
        · simp [Set.indicator, hω, hs1]
        · simp [Set.indicator, hω, hs0]
      rw [hpre]
      simp
    · have hpre :
          (Set.indicator A (fun _ : Ω => (1 : ℝ))) ⁻¹' s = A := by
        ext ω
        by_cases hω : ω ∈ A
        · simp [Set.indicator, hω, hs1]
        · simp [Set.indicator, hω, hs0, Set.mem_compl_iff]
      rw [hpre]
      exact hFirst B hB
  · by_cases hs0 : (0 : ℝ) ∈ s
    · have hpre :
          (Set.indicator A (fun _ : Ω => (1 : ℝ))) ⁻¹' s = Aᶜ := by
        ext ω
        by_cases hω : ω ∈ A
        · simp [Set.indicator, hω, hs1]
        · simp [Set.indicator, hω, hs0]
      rw [hpre]
      exact hSecond B hB
    · have hpre :
          (Set.indicator A (fun _ : Ω => (1 : ℝ))) ⁻¹' s = ∅ := by
        ext ω
        by_cases hω : ω ∈ A
        · simp [Set.indicator, hω, hs1]
        · simp [Set.indicator, hω, hs0]
      rw [hpre]
      simp
