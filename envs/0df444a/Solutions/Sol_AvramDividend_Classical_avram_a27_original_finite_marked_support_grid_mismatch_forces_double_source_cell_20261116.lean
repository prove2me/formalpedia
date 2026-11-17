-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_finite_marked_support_grid_mismatch_forces_double_source_cell_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:21:31.44649+00:00
-- url     : https://prove2.me/submissions/f438f667-5fe3-4360-827a-57143dd978eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_marked_support_monotone_halfopen_grid_disjoint_partition_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_disjoint_finite_grid_occupied_mismatch_forces_double_cell_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
       0 < u ∧ u ≤ T ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B)
    (n : ℕ) (hn : 0 < n) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    S.card ≠ ((Finset.range n).filter (fun i : ℕ =>
      NX (Ioc ((i : ℝ≥0) * δ)
        (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) ≠ 0)).card →
    ∃ i ∈ Finset.range n,
      (2 : ℝ) ≤
        (NX (Ioc ((i : ℝ≥0) * δ)
          (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)).toReal := by
  classical
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℝ≥0 := T / (n : ℝ≥0)
  let Z : ℕ := ((Finset.range n).filter (fun i : ℕ =>
    NX (Ioc ((i : ℝ≥0) * δ)
      (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) ≠ 0)).card
  change S.card ≠ Z →
    ∃ i ∈ Finset.range n,
      (2 : ℝ) ≤ (NX (Ioc ((i : ℝ≥0) * δ)
        (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)).toReal
  intro hDiff
  let u : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
  let F : ℕ → Finset ℝ≥0 := fun i =>
    S.filter (fun t => t ∈ Ioc (u i) (u (i + 1)))
  have hu : Monotone u := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) bot_le
  have hu0 : u 0 = 0 := by simp [u]
  have hun : u n = T := by
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    dsimp only [u, δ]
    field_simp [hn0]
  have hSIn : ∀ t ∈ S, t ∈ Ioc (u 0) (u n) := by
    intro t ht
    have hh := (hS t).mp ht
    simpa only [hu0, hun] using
      (show t ∈ Ioc (0 : ℝ≥0) T from ⟨hh.1, hh.2.1⟩)
  have hPart :=
    avram_a27_finite_marked_support_monotone_halfopen_grid_disjoint_partition_20261116
      u hu n S hSIn
  have hCover : (Finset.range n).biUnion F = S := hPart.1
  have hDisj : ((Finset.range n : Set ℕ).PairwiseDisjoint F) := hPart.2
  have hCell (i : ℕ) (hi : i ∈ Finset.range n) :
      NX (Ioc (u i) (u (i + 1)) ×ˢ B) =
        ((F i).card : ℝ≥0∞) := by
    have hiN : i < n := Finset.mem_range.mp hi
    have ht : u (i + 1) ≤ T := by
      calc
        u (i + 1) ≤ u n := hu (Nat.succ_le_iff.mpr hiN)
        _ = T := hun
    simpa only [NX, F, Set.mem_Ioc] using
      (avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
        X ω T B hB S hS (u i) (u (i + 1)) (hu (Nat.le_succ i)) ht)
  have hZ : Z =
      ((Finset.range n).filter (fun i => (F i).Nonempty)).card := by
    dsimp only [Z]
    congr 1
    ext i
    by_cases hi : i ∈ Finset.range n
    · simp only [Finset.mem_filter, hi, true_and]
      change NX (Ioc (u i) (u (i + 1)) ×ˢ B) ≠ 0 ↔ (F i).Nonempty
      rw [hCell i hi]
      simp
      exact (Finset.nonempty_iff_ne_empty).symm
    · simp [Finset.mem_filter, hi]
  have hBad : S.card ≠
      ((Finset.range n).filter (fun i => (F i).Nonempty)).card := by
    simpa only [hZ] using hDiff
  obtain ⟨i, hi, hTwo⟩ :=
    avram_a26_disjoint_finite_grid_occupied_mismatch_forces_double_cell_20261116
      (Finset.range n) S F hCover hDisj hBad
  refine ⟨i, hi, ?_⟩
  have hiEq := hCell i hi
  change (2 : ℝ) ≤ (NX (Ioc (u i) (u (i + 1)) ×ˢ B)).toReal
  rw [hiEq]
  exact_mod_cast hTwo
