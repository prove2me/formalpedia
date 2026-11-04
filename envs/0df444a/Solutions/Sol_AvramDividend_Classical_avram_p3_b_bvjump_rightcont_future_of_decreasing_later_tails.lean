-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:32:00.190734+00:00
-- url     : https://prove2.me/submissions/50db17bf-df30-422f-a70f-40eb46937337

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
    (i : ℝ≥0) (A : Set Ω) (B : Set ℝ) (hB : MeasurableSet B)
    (r : ℕ → ℝ≥0) (hr : Antitone r)
    (hrAbove : ∀ n, i < r n)
    (hrCofinal : ∀ u : ℝ≥0, i < u → ∃ n, r n < u)
    (hAr : ∀ n, MeasurableSet[𝓕.rightCont (r n)] A)
    (hTail : ∀ n, M ((Ioi (r n) ×ˢ A) ×ˢ B) =
                  N ((Ioi (r n) ×ˢ A) ×ˢ B)) :
    M ((Ioi i ×ˢ A) ×ˢ B) = N ((Ioi i ×ˢ A) ×ˢ B) := by
  let E : ℕ → Set ((ℝ≥0 × Ω) × ℝ) :=
    fun n => ((Ioi (r n) ×ˢ A) ×ˢ B)
  have hmono : Monotone E := by
    intro m n hmn p hp
    change (r m < p.1.1 ∧ p.1.2 ∈ A) ∧ p.2 ∈ B at hp
    change (r n < p.1.1 ∧ p.1.2 ∈ A) ∧ p.2 ∈ B
    exact ⟨⟨lt_of_le_of_lt (hr hmn) hp.1.1, hp.1.2⟩, hp.2⟩
  have hCover : (⋃ n, E n) = ((Ioi i ×ˢ A) ×ˢ B) := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      change (r n < p.1.1 ∧ p.1.2 ∈ A) ∧ p.2 ∈ B at hn
      exact ⟨⟨lt_trans (hrAbove n) hn.1.1, hn.1.2⟩, hn.2⟩
    · intro hp
      rcases hp with ⟨⟨hio, ha⟩, hb⟩
      obtain ⟨n, hn⟩ := hrCofinal p.1.1 hio
      exact ⟨n, ⟨⟨hn, ha⟩, hb⟩⟩
  have hEm : ∀ n, MeasurableSet[
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (E n) := by
    intro n
    have hp : MeasurableSet[𝓕.rightCont.predictable]
        (Ioi (r n) ×ˢ A) :=
      measurableSet_predictable_Ioi_prod (hAr n)
    exact hp.prod hB
  have hEq : ∀ n, M (E n) = N (E n) := by
    intro n
    exact hTail n
  calc
    M ((Ioi i ×ˢ A) ×ˢ B) = M (⋃ n, E n) := by rw [hCover]
    _ = ⨆ n, M (E n) := hmono.measure_iUnion
    _ = ⨆ n, N (E n) := iSup_congr hEq
    _ = N (⋃ n, E n) := (hmono.measure_iUnion).symm
    _ = N ((Ioi i ×ˢ A) ×ˢ B) := by rw [hCover]
