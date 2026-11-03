-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_dense_grid_cadlag_borel_intrinsic_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:27:28.717062+00:00
-- url     : https://prove2.me/submissions/a746b114-727e-4342-be24-a78d79e137a5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_existing_strict_left_limit_is_canonical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- A dense source grid gives the exact measurable Borel marked intrinsic count;
zero marks are explicitly excluded even when the Borel set contains zero. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u →
          ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard : ℝ≥0∞) = F Y := by
  classical
  let B₀ : Set ℝ := B \ {0}
  have hB₀ : MeasurableSet B₀ := hB.diff (measurableSet_singleton (0 : ℝ))
  obtain ⟨time, htime, hCover⟩ :=
    avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
      grid hdense pairs hpairs
  obtain ⟨mark, hmark, hExact, hSeriesMeas⟩ :=
    avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
      grid hdense time htime ε hεpos hε T B₀ hB₀
  refine ⟨_, hSeriesMeas, ?_⟩
  intro Y hRight hLeft
  have hCanonical : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by
    intro u hu
    exact avram_wave7_01_existing_strict_left_limit_is_canonical
      Y u hu (hLeft u hu)
  let S : Set ℝ≥0 :=
    {v | 0 < v ∧ v ≤ T ∧
      Y v - Function.leftLim Y v ≠ 0 ∧
      Y v - Function.leftLim Y v ∈ B}
  have hScover : S ⊆ Set.range (fun k : ℕ => time k Y) := by
    intro u hu
    obtain ⟨huPos, huT, huJump, huMark⟩ := hu
    exact hCover Y hRight hCanonical u huPos huJump
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
        simp [S, B₀, hp, heq, and_comm, and_left_comm, and_assoc]
      · simp [S, hp]
