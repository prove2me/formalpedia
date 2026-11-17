-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_cadlag_candidate_firstoccurrence_window_Borel_encard_eq_tsum_v2_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:47:13.286908+00:00
-- url     : https://prove2.me/submissions/d26641e9-1fa3-4ca1-a3be-a63bb4da0bf2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_existing_strict_left_limit_is_canonical
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
theorem solution
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (hCover : ∀ Y : ℝ≥0 → ℝ,
      (∀ u, ContinuousWithinAt Y (Ici u) u) →
      (∀ u, 0 < u →
        Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u))) →
      ∀ u, 0 < u → Y u - Function.leftLim Y u ≠ 0 →
        ∃ k : ℕ, time k Y = u)
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hExact : ∀ k (Y : ℝ≥0 → ℝ), 0 < time k Y →
      ContinuousWithinAt Y (Ici (time k Y)) (time k Y) →
      Tendsto Y (𝓝[<] (time k Y))
        (𝓝 (Function.leftLim Y (time k Y))) →
      mark k Y = Y (time k Y) - Function.leftLim Y (time k Y))
    (s T : ℝ≥0) (B : Set ℝ) :
    ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({v : ℝ≥0 | s < v ∧ v ≤ T ∧
        Y v - Function.leftLim Y v ≠ 0 ∧
        Y v - Function.leftLim Y v ∈ B}).encard =
        ∑' k : ℕ,
          if s < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B \ {0} ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (1 : ℝ≥0∞) else 0 := by
  classical
  intro Y hRight hLeft
  have hCanonical : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by
    intro u hu
    exact avram_wave7_01_existing_strict_left_limit_is_canonical
      Y u hu (hLeft u hu)
  let S : Set ℝ≥0 :=
    {v | s < v ∧ v ≤ T ∧
      Y v - Function.leftLim Y v ≠ 0 ∧
      Y v - Function.leftLim Y v ∈ B}
  have hScover : S ⊆ Set.range (fun k : ℕ => time k Y) := by
    intro u hu
    obtain ⟨huStart, huT, huJump, huMark⟩ := hu
    exact hCover Y hRight hCanonical u
      (lt_of_le_of_lt bot_le huStart) huJump
  have hCard :=
    avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
      (fun k : ℕ => time k Y) S hScover
  calc
    (S.encard : ℝ≥0∞) = ∑' k : ℕ,
        if time k Y ∈ S ∧ (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then (1 : ℝ≥0∞) else 0 := by
      rw [hCard]
      apply tsum_congr
      intro k
      by_cases hk : time k Y ∈ S ∧
          (∀ j : ℕ, j < k → time j Y ≠ time k Y)
      · simp only [if_pos hk]
      · simp only [if_neg hk]
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hp : 0 < time k Y
      · have heq := hExact k Y hp (hRight (time k Y))
          (hCanonical (time k Y) hp)
        simp [S, hp, heq, and_comm, and_left_comm, and_assoc]
      · have hs : ¬ s < time k Y := by
          intro hs
          exact hp (lt_of_le_of_lt bot_le hs)
        simp [S, hp, hs]
