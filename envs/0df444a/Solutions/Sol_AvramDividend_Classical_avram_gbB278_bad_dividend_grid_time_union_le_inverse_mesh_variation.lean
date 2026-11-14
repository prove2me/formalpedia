-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB278_bad_dividend_grid_time_union_le_inverse_mesh_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:01:35.021214+00:00
-- url     : https://prove2.me/submissions/09bd293f-f788-4a2f-9d02-94836c052a9a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB257_monotone_grid_large_dividend_cell_count_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

private theorem volume_union_local (I : Finset ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
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

theorem solution (d : ℕ → ℝ) (hd : Monotone d) (n m : ℕ) (hm : 0 < m)
:
    volume (⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
       (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)),
      Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4)))) ≤
      ENNReal.ofReal ((d (n * m ^ 4) - d 0) / (m : ℝ)) := by
  let I : Finset ℕ := (Finset.range (n * m ^ 4)).filter
    (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hRaw :=
    volume_union_local I δ hδ
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hEps : (0 : ℝ) < 1 / ((m : ℝ) ^ 3) := by positivity
  have hBase := avram_gbB257_monotone_grid_large_dividend_cell_count_bound
    d hd (1 / ((m : ℝ) ^ 3)) hEps (n * m ^ 4)
  have hCount : (I.card : ℝ) * δ ≤
      (d (n * m ^ 4) - d 0) / (m : ℝ) := by
    calc
      (I.card : ℝ) * δ =
          (I.card : ℝ) * (1 / ((m : ℝ) ^ 3)) * (1 / (m : ℝ)) := by
            dsimp [δ]
            field_simp
      _ ≤ (d (n * m ^ 4) - d 0) * (1 / (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [I] using hBase) (by positivity)
      _ = _ := by ring
  have hCast : (I.card : ℝ≥0∞) * ENNReal.ofReal δ =
      ENNReal.ofReal ((I.card : ℝ) * δ) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    norm_cast
  change volume (⋃ i ∈ I, Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ)) ≤ _
  calc
    _ ≤ (I.card : ℝ≥0∞) * ENNReal.ofReal δ := hRaw
    _ = ENNReal.ofReal ((I.card : ℝ) * δ) := hCast
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by exact hCount)
