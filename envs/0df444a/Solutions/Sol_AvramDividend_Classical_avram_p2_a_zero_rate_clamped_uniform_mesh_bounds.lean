-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:03:12.57145+00:00
-- url     : https://prove2.me/submissions/96bcdeb0-2dc7-48b6-95e3-7703fd311bd9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Extend a finite uniform mesh to all natural indices by degenerate
terminal cells, retaining horizon and width bounds. -/
theorem solution
    (T δ : ℝ≥0) (n i : ℕ)
    (hcover : ((n : ℝ≥0) + 1) * δ = T) :
    (if i ≤ n then (i : ℝ≥0) * δ else T) ≤ T ∧
    (if i ≤ n then (i : ℝ≥0) * δ else T) ≤
      (if i ≤ n then (((i + 1 : ℕ) : ℝ≥0) * δ) else T) ∧
    (if i ≤ n then (((i + 1 : ℕ) : ℝ≥0) * δ) else T) ≤
      (if i ≤ n then (i : ℝ≥0) * δ else T) + δ := by
  by_cases hi : i ≤ n
  · simp only [hi, ite_true]
    have hn : (i : ℝ≥0) ≤ (n : ℝ≥0) + 1 := by
      exact_mod_cast Nat.le_succ_of_le hi
    have hbound : (i : ℝ≥0) * δ ≤ T :=
      (mul_le_mul_of_nonneg_right hn bot_le).trans hcover.le
    have hstep : (((i + 1 : ℕ) : ℝ≥0) * δ) =
        (i : ℝ≥0) * δ + δ := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    refine ⟨hbound, ?_, ?_⟩
    · rw [hstep]
      exact le_add_of_nonneg_right bot_le
    · rw [hstep]
  · simp only [hi, ite_false]
    exact ⟨le_refl _, le_refl _, le_add_of_nonneg_right bot_le⟩
