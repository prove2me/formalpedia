-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_finite_rectangles_to_original_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:33:27.635303+00:00
-- url     : https://prove2.me/submissions/8adcde82-5d8a-48b4-9865-d6f6078910f7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hCellMeas : ∀ (s t : ℝ≥0) (A : Set Ω) (B : Set ℝ),
      MeasurableSet[𝓕 s] A → MeasurableSet B →
      MeasurableSet[(@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
        ((Ioc s t ×ˢ A) ×ˢ B))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M ((Ioi s ×ˢ A) ×ˢ B) = N ((Ioi s ×ˢ A) ×ˢ B) := by
  let E : ℕ → Set ((ℝ≥0 × Ω) × ℝ) :=
    fun n => ((Ioc s (s + (n : ℝ≥0)) ×ˢ A) ×ˢ B)
  have hmono : Monotone E := by
    intro m n hmn p hp
    change ((s < p.1.1 ∧ p.1.1 ≤ s + (m : ℝ≥0)) ∧
      p.1.2 ∈ A) ∧ p.2 ∈ B at hp
    rcases hp with ⟨⟨⟨hlo, hhi⟩, ha⟩, hb⟩
    change ((s < p.1.1 ∧ p.1.1 ≤ s + (n : ℝ≥0)) ∧
      p.1.2 ∈ A) ∧ p.2 ∈ B
    refine ⟨⟨⟨hlo, ?_⟩, ha⟩, hb⟩
    have hmn' : (m : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hmn
    exact hhi.trans (add_le_add_right hmn' s)
  have hCover : (⋃ n, E n) = ((Ioi s ×ˢ A) ×ˢ B) := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      change ((s < p.1.1 ∧ p.1.1 ≤ s + (n : ℝ≥0)) ∧
        p.1.2 ∈ A) ∧ p.2 ∈ B at hn
      exact ⟨⟨hn.1.1.1, hn.1.2⟩, hn.2⟩
    · intro hp
      rcases hp with ⟨⟨hlo, ha⟩, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt p.1.1
      refine ⟨n, ?_⟩
      change ((s < p.1.1 ∧ p.1.1 ≤ s + (n : ℝ≥0)) ∧
        p.1.2 ∈ A) ∧ p.2 ∈ B
      refine ⟨⟨⟨hlo, ?_⟩, ha⟩, hb⟩
      have hs0 : (0 : ℝ≥0) ≤ s := zero_le
      exact (le_of_lt hn).trans (le_add_of_nonneg_left hs0)
  have hEm : ∀ n, MeasurableSet[
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (E n) := by
    intro n
    exact hCellMeas s (s + n) A B hA hB
  have hEq : ∀ n, M (E n) = N (E n) := by
    intro n
    have hn0 : (0 : ℝ≥0) ≤ (n : ℝ≥0) := zero_le
    exact hRect s (s + n) (le_add_of_nonneg_right hn0) A hA B hB
  calc
    M ((Ioi s ×ˢ A) ×ˢ B) = M (⋃ n, E n) := by rw [hCover]
    _ = ⨆ n, M (E n) := hmono.measure_iUnion
    _ = ⨆ n, N (E n) := iSup_congr hEq
    _ = N (⋃ n, E n) := (hmono.measure_iUnion).symm
    _ = N ((Ioi s ×ˢ A) ×ˢ B) := by rw [hCover]
