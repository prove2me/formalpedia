-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva77_original_uniform_source_terminal_clock_eq_strict_cash_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:11:54.074114+00:00
-- url     : https://prove2.me/submissions/547a8440-feb2-4abc-a26d-dc6099bb4d40

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n : ℕ,
      (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2) ∧
      (u n (n + 1) : ℝ) < T := by
  intro n
  have hd : (n : ℝ) + 2 ≠ 0 := by positivity
  have heq : (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2) := by
    rw [huniform n (n + 1)]
    push_cast
    field_simp
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  exact
    ((avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).1 n).2
