-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep8_original_BV_unmarked_grid_jump_mass_le_negative_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:18:44.978197+00:00
-- url     : https://prove2.me/submissions/1700fa1c-1063-4444-ad9d-61ce02e1f147

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℝ≥0) (cells : Finset ℕ)
    (marked : Finset ℝ≥0) (hu : StrictMono u)
    (hBound : ∀ i ∈ cells, u (i + 1) ≤ T)
    (hAvoid : ∀ i ∈ cells, ∀ t ∈ marked,
      ¬ (u i < t ∧ t ≤ u (i + 1))) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
      let j : ℝ≥0 → ℝ := fun t =>
        if 0 < t ∧ t ≤ T then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
      Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) ≤
        ∑' t : ℝ≥0, if t ∈ marked then 0 else j t := by
  have hSumm := avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV
  have hInterval :=
    avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity X hBV
  filter_upwards [hSumm, hInterval] with ω hs hi
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
  let j : ℝ≥0 → ℝ := fun t =>
    if 0 < t ∧ t ≤ T then
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
  change Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) ≤
    ∑' t : ℝ≥0, if t ∈ marked then 0 else j t
  have hj : Summable j := by
    simpa only [j] using (hs 0 T (show (0 : ℝ≥0) ≤ T from zero_le)).1
  have hjnonneg (t : ℝ≥0) : 0 ≤ j t := by
    by_cases ht : 0 < t ∧ t ≤ T
    · simpa [j, ht] using
        (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
          X ω t ht.1).1
    · simp [j, ht]
  have hUnique :
      ∀ t i, i ∈ cells → ∀ k, k ∈ cells →
        (u i < t ∧ t ≤ u (i + 1)) →
        (u k < t ∧ t ≤ u (k + 1)) → i = k := by
    intro t i _ k _ hci hck
    rcases lt_trichotomy i k with hik | heq | hki
    · have hb : u (i + 1) ≤ u k :=
        hu.monotone (Nat.succ_le_of_lt hik)
      exact False.elim ((not_lt_of_ge (hci.2.trans hb)) hck.1)
    · exact heq
    · have hb : u (k + 1) ≤ u i :=
        hu.monotone (Nat.succ_le_of_lt hki)
      exact False.elim ((not_lt_of_ge (hck.2.trans hb)) hci.1)
  have hCell (i : ℕ) (hiCell : i ∈ cells) :
      J (u (i + 1)) - J (u i) =
        ∑' t : ℝ≥0, if u i < t ∧ t ≤ u (i + 1) then j t else 0 := by
    have hb : u (i + 1) ≤ T := hBound i hiCell
    have htime : u i ≤ u (i + 1) := hu.monotone (Nat.le_succ i)
    have hJ := hi (u i) (u (i + 1)) htime
    change J (u (i + 1)) = J (u i) +
      (∑' t : ℝ≥0, if u i < t ∧ t ≤ u (i + 1) then
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0) at hJ
    have hSeries :
        (∑' t : ℝ≥0, if u i < t ∧ t ≤ u (i + 1) then j t else 0) =
        (∑' t : ℝ≥0, if u i < t ∧ t ≤ u (i + 1) then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0) := by
      apply tsum_congr
      intro t
      by_cases ht : u i < t ∧ t ≤ u (i + 1)
      · have ht0 : 0 < t := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ u i from zero_le) ht.1
        have htT : t ≤ T := ht.2.trans hb
        simp [j, ht, ht0, htT]
      · simp [ht]
    rw [hSeries, hJ]
    ring
  have hMass :=
    avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
      j hj hjnonneg marked cells
      (fun i t => u i < t ∧ t ≤ u (i + 1)) hUnique hAvoid
  calc
    Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) =
      (∑ i ∈ cells, ∑' t : ℝ≥0,
        if u i < t ∧ t ≤ u (i + 1) then j t else 0) := by
          apply Finset.sum_congr rfl
          intro i hiCell
          exact hCell i hiCell
    _ ≤ ∑' t : ℝ≥0, if t ∈ marked then 0 else j t := by
      convert hMass using 1
      · apply Finset.sum_congr rfl
        intro i hi
        apply tsum_congr
        intro t
        by_cases ht : u i < t ∧ t ≤ u (i + 1) <;> simp [ht]
      · apply tsum_congr
        intro t
        by_cases ht : t ∈ marked <;> simp [ht]
