-- Prove2me | solution 1 for FiniteTriangular.sum_range_744
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:46.363479+00:00
-- url     : https://prove2.me/submissions/f00ca2a1-2970-452a-933c-19081a1ebc8d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 744, k = 276396 := by
  rw [sum_range_id]
