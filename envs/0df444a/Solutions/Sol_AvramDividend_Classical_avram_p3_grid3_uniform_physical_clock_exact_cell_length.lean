-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_exact_cell_length
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:55:35.18621+00:00
-- url     : https://prove2.me/submissions/8069a7cf-b065-4c9d-bd98-bc86d459d29e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (T : ℝ≥0) (m i : ℕ) (hi : i < m + 1) :
    let u : ℕ → ℝ≥0 := fun j =>
      ((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
    u (i + 1) - u i = T / (m + 1) := by
  have hi0 : i ≤ m + 1 := Nat.le_of_lt hi
  have hi1 : i + 1 ≤ m + 1 := Nat.succ_le_of_lt hi
  change ((min (i + 1) (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1 : ℝ≥0)) -
    ((min i (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1 : ℝ≥0)) = T / (m + 1 : ℝ≥0)
  simp only [min_eq_left hi0, min_eq_left hi1, Nat.cast_add,
    Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left]
