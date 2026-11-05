-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_uniform_grid_image_le_indicator_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:52:07.080653+00:00
-- url     : https://prove2.me/submissions/60ecf3cd-fb06-467a-99ca-9794bd3853fa

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    ((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℝ≥0∞)
    ≤ ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℝ≥0∞) else 0) := by
  let d : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  let s : Finset ℕ := Finset.range (n + 1)
  let grid : ℕ → ℝ≥0 := fun i => ((i + 1 : ℕ) : ℝ≥0) * d
  let marked : ℝ≥0 → Prop := fun t => Y t - Y (t - d) < -ε / 2
  have hshift (i : ℕ) : grid i - d = (i : ℝ≥0) * d := by
    dsimp [grid]
    simp [Nat.cast_add, add_mul]
  have hcount :=
    avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
      s grid marked
  change (((s.image grid).filter marked).card : ℝ≥0∞) ≤
    ∑ i ∈ s, (if Y (grid i) - Y ((i : ℝ≥0) * d) < -ε / 2
      then (1 : ℝ≥0∞) else 0)
  calc
    _ ≤ ((s.filter (fun i => marked (grid i))).card : ℝ≥0∞) := by
      exact_mod_cast hcount
    _ = ∑ i ∈ s, (if marked (grid i) then (1 : ℝ≥0∞) else 0) :=
      avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
        s (fun i => marked (grid i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [marked]
      rw [hshift i]
