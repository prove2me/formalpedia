-- Prove2me | solution 1 for FiniteTriangular.sum_range_537
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:05.367865+00:00
-- url     : https://prove2.me/submissions/27a231e9-ccca-43a2-a3bc-62bfb136ef8a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 537, k = 143916 := by
  rw [sum_range_id]
