-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_uniform_nnreal_real_mesh_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:53:42.044404+00:00
-- url     : https://prove2.me/submissions/e3d518d2-f7d7-4d16-a67f-323cb66184fa

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-! Exact grid-width convention bridge for P2-H and P2-J. -/
theorem solution
    (T : ℝ≥0) (n : ℕ) :
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / ((n : ℝ≥0) + 1) := by
  have hT : 0 ≤ (T : ℝ) := T.coe_nonneg
  have hn : 0 ≤ (n : ℝ) := by positivity
  calc
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      Real.toNNReal (T : ℝ) / Real.toNNReal ((n : ℝ) + 1) :=
        Real.toNNReal_div hT
    _ = T / ((n : ℝ≥0) + 1) := by
      rw [Real.toNNReal_add hn (by norm_num)]
      simp
