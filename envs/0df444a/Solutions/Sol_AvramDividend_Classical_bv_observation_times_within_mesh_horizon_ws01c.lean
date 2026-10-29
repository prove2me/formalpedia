-- Prove2me | solution 1 for AvramDividend.Classical.bv_observation_times_within_mesh_horizon_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:04:07.553258+00:00
-- url     : https://prove2.me/submissions/5d41b117-b300-4406-83ea-1eb91e96a0bc

import Mathlib

open Set
open scoped NNReal

theorem solution
    (h : ℝ≥0) (M : ℕ) :
    ∀ t ∈ (List.range (M + 1)).map
        (fun k : ℕ => (k : ℝ≥0) * h),
      t ≤ (M : ℝ≥0) * h := by
  intro t ht
  simp only [List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  have : (k : ℝ≥0) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp hk
  exact mul_le_mul_of_nonneg_right this zero_le
