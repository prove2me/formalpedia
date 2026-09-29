-- Prove2me | solution 1 for Erdos68.factorial_moment_window_escape
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-25T19:34:57.2653+00:00
-- url     : https://prove2.me/submissions/2af8aa37-d14f-410b-a20c-f634a153a56c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos68_factorial_moment_window_escape_witness

open scoped BigOperators
open Erdos68

theorem solution :
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      Int.fract (∑ n ∈ Finset.range (M - 1),
          (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) ∉
        Set.Ioo (1 - 1 / (M : ℚ)) (1 - 1 / ((M : ℚ) + 1)) := by
  intro N
  exact factorial_moment_window_escape_witness N
