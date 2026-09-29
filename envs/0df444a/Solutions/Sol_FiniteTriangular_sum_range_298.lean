-- Prove2me | solution 1 for FiniteTriangular.sum_range_298
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:04.804366+00:00
-- url     : https://prove2.me/submissions/a72a6f05-8791-496a-9a0c-42e149838f6d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 298, k = 44253 := by
  rw [sum_range_id]
