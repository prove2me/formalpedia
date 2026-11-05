-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_cell_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:00:09.599131+00:00
-- url     : https://prove2.me/submissions/93812e77-c9c3-48c2-a0d1-38f04062d879

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Uniform source grid cells have chronological boundaries inside the physical horizon. -/
theorem solution (T : ℝ≥0) (k : ℕ) (i : Fin (k + 1)) :
    (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) ≤
        (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1))) ∧
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1))) ≤ T := by
  have hden : (k : ℝ≥0) + 1 ≠ 0 := by positivity
  constructor
  · gcongr
    exact_mod_cast (Nat.le_succ i.val)
  · calc
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1))) ≤
          ((k : ℝ≥0) + 1) * (T / ((k : ℝ≥0) + 1)) := by
        gcongr
        exact_mod_cast (Nat.succ_le_of_lt i.isLt)
      _ = T := by field_simp [hden]
