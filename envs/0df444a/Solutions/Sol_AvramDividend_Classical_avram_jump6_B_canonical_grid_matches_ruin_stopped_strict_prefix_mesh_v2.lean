-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_grid_matches_ruin_stopped_strict_prefix_mesh_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:08:40.582423+00:00
-- url     : https://prove2.me/submissions/12d6dba4-a432-4bff-abf3-058fbc6505fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (n j i : ℕ) (ρ : ℝ≥0) (hρ : ρ ≤ (n : ℝ≥0))
    (hi : i ≤ (n + 1) * (j + 1)) :
    min (((min i ((n + 1) * (j + 1)) : ℕ) : ℝ≥0) *
      (((n + 1 : ℕ) : ℝ≥0) /
        (((n + 1) * (j + 1) : ℕ) : ℝ≥0)))
      (min ρ ((n + 1 : ℕ) : ℝ≥0)) =
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ := by
  have hρT : ρ ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    exact le_trans hρ (by exact_mod_cast Nat.le_succ n)
  have hn0 : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
  have hj0 : ((j + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
  have hfrac :
      ((n + 1 : ℕ) : ℝ≥0) /
        (((n + 1) * (j + 1) : ℕ) : ℝ≥0) =
        1 / ((j + 1 : ℕ) : ℝ≥0) := by
    rw [Nat.cast_mul]
    field_simp [hn0, hj0]
  rw [min_eq_left hi, min_eq_left hρT, hfrac]
  ring
