-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_time_mem_finite_nnreal_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:57:00.502336+00:00
-- url     : https://prove2.me/submissions/d5f835d9-e66a-428f-a117-7721f28a97c4

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid
import Mathlib.Data.Finset.Image
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- A bounded dyadic approximation lies in the explicit finite time grid. -/
theorem solution
    (t T : ℝ≥0) (ht : t ≤ T) (n : ℕ) :
    (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n ∈
      (Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) + 1)).image
        (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
  apply Finset.mem_image.mpr
  exact ⟨Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n),
    dyadic_ceiling_index_mem_finite_grid t T ht n, rfl⟩
