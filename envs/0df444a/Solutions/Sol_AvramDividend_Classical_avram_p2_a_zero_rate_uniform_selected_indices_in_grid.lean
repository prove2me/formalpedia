-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_selected_indices_in_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:29:46.334792+00:00
-- url     : https://prove2.me/submissions/4f5423b7-ab5c-440a-85ce-65a9d2e044b8

import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Every chosen original jump cell is a member of the actual finite
source-grid index set when its index is bounded by the resolution. -/
theorem solution
    (F : Finset ℝ≥0) (idx : ℝ≥0 → ℕ → ℕ)
    (hidx : ∀ t ∈ F, ∀ n : ℕ, idx t n ≤ n) :
    ∀ n : ℕ, ∀ t ∈ F, idx t n ∈ Finset.range (n + 1) := by
  intro n t ht
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hidx t ht n))
