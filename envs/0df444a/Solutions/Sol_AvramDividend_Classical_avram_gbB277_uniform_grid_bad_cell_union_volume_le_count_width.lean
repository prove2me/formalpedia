-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB277_uniform_grid_bad_cell_union_volume_le_count_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:15:33.447576+00:00
-- url     : https://prove2.me/submissions/38d94e44-0738-4411-b1f4-d5045c68e81c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- The time union of finitely many equal-width positive mesh cells is bounded by its count times width. -/
theorem solution (I : Finset ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (⋃ i ∈ I, Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ)) ≤
      (I.card : ℝ≥0∞) * ENNReal.ofReal δ := by
  calc
    volume (⋃ i ∈ I, Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ)) ≤
      ∑ i ∈ I, volume (Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ)) :=
        measure_biUnion_finset_le I _
    _ = ∑ _i ∈ I, ENNReal.ofReal δ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.volume_Ioo]
      congr 1
      ring
    _ = (I.card : ℝ≥0∞) * ENNReal.ofReal δ := by
      simp [Finset.sum_const, nsmul_eq_mul]
