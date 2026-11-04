-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:41:12.569065+00:00
-- url     : https://prove2.me/submissions/0f82fe2e-103e-4502-893f-595816b01461

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_enat_indicator_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENat BigOperators
attribute [local instance] Classical.propDecidable

/-- Marked mesh endpoint ENat count is bounded by source cell indicators. -/
theorem solution (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    ((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞)
    ≤ ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℕ∞) else 0) := by
  classical
  letI : DecidableEq ℝ≥0 := fun a b => Classical.propDecidable (a = b)
  let w : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  let f : ℕ → ℝ≥0 := fun j => ((j + 1 : ℕ) : ℝ≥0) * w
  let p : ℝ≥0 → Prop := fun t => Y t - Y (t - w) < -ε / 2
  have hc := avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
    (Finset.range (n + 1)) f p
  have hs := avram_p2_34dbea70_filter_card_eq_enat_indicator_sum
    (Finset.range (n + 1)) (fun i => p (f i))
  have hmain :
      ((((Finset.range (n + 1)).image f).filter p).card : ℕ∞) ≤
        ∑ i ∈ Finset.range (n + 1),
          (if p (f i) then (1 : ℕ∞) else 0) := by
    calc
      _ ≤ (((Finset.range (n + 1)).filter (fun i => p (f i))).card : ℕ∞) := by
        exact_mod_cast hc
      _ = _ := hs
  have hstep (i : ℕ) :
      (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        (T / ((n : ℝ≥0) + 1)) =
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) := by
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_right]
  simpa only [f, p, w, hstep] using hmain
