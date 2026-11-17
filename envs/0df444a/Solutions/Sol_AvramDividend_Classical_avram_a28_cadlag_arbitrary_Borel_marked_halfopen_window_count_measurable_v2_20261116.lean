-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_cadlag_arbitrary_Borel_marked_halfopen_window_count_measurable_v2_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:51:46.82953+00:00
-- url     : https://prove2.me/submissions/70d89151-469c-4e90-81e0-56c4e24239a2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a28_cadlag_candidate_firstoccurrence_window_Borel_encard_eq_tsum_v2_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a28_measurable_countable_dedup_marked_window_series_v2_20261116
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

/-- Intrinsic càdlàg nonzero Borel jump counts extend measurably over
all product-coordinate real paths without any finite-activity assumption. -/
theorem solution
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | s < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by
  classical
  obtain ⟨grid, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  obtain ⟨pairs, hpairs⟩ := exists_surjective_nat (ℕ × ℚ)
  let ε : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos (by norm_num) (by positivity)
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ≥0)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let B₀ : Set ℝ := B \ {0}
  have hB₀ : MeasurableSet B₀ := hB.diff (measurableSet_singleton (0 : ℝ))
  obtain ⟨time, htime, hCover⟩ :=
    avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
      grid hdense pairs hpairs
  obtain ⟨mark, hmark, hExact, _⟩ :=
    avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
      grid hdense time htime ε hεpos hε T B₀ hB₀
  have hSeriesMeas :=
    avram_a28_measurable_countable_dedup_marked_window_series_v2_20261116
      s T B₀ hB₀ time htime mark hmark
  refine ⟨_, hSeriesMeas, ?_⟩
  intro Y hRight hLeft
  have hCard :=
    avram_a28_cadlag_candidate_firstoccurrence_window_Borel_encard_eq_tsum_v2_20261116
      time hCover mark hExact s T B Y hRight hLeft
  rw [hCard]
  apply tsum_congr
  intro k
  have hc : (s < time k Y ∧ time k Y ≤ T ∧
      mark k Y ∈ B₀ ∧ (∀ j : ℕ, j < k → time j Y ≠ time k Y)) ↔
      (s < time k Y ∧ time k Y ≤ T ∧
      mark k Y ∈ B \ {0} ∧ (∀ j : ℕ, j < k → time j Y ≠ time k Y)) := by
    change _ ↔ _
    simp only [B₀]
  by_cases h : s < time k Y ∧ time k Y ≤ T ∧
      mark k Y ∈ B₀ ∧ (∀ j : ℕ, j < k → time j Y ≠ time k Y)
  · simp only [if_pos h, if_pos (hc.mp h)]
  · simp only [if_neg h, if_neg (fun hs => h (hc.mpr hs))]
