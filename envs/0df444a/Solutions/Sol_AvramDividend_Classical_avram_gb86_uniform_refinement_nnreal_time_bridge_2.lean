-- Prove2me | solution 2 for AvramDividend.Classical.avram_gb86_uniform_refinement_nnreal_time_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:33:07.236822+00:00
-- url     : https://prove2.me/submissions/88e1a9b3-1e98-4aaa-804a-dc91b54639fc

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

theorem solution (n m b i : ℕ) (hb : 0 < b) :
    (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) =
    ((i * b : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)) := by
  have hm : (m + 1 : ℝ≥0) ≠ 0 := by positivity
  have hbb : (b : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  simp only [Nat.cast_mul]
  field_simp
