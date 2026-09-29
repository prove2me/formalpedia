-- Prove2me | solution 1 for Erdos68.factorial_moment_window_escape_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-25T19:42:05.532981+00:00
-- url     : https://prove2.me/submissions/bb5211ba-b73c-4a78-a0d5-aac412c34002
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos68_factorial_moment_partial_sum_bound

open scoped BigOperators
open Erdos68

theorem solution :
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      Int.fract (∑ n ∈ Finset.range (M - 1),
          (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) ∉
        Set.Ioo (1 - 1 / (M : ℚ)) (1 - 1 / ((M : ℚ) + 1)) := by
  intro N
  use (max N 3)
  refine ⟨by omega, ?_⟩
  intro h_in
  rw [Set.mem_Ioo] at h_in
  exact factorial_moment_partial_sum_bound (max N 3) (by omega) h_in.1 h_in.2
