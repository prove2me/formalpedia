-- Prove2me | solution 1 for FiniteTriangular.sum_range_1076
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:32.212819+00:00
-- url     : https://prove2.me/submissions/1cd64c19-4da4-4ef9-be43-57d224b0371f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1076, k = 578350 := by
  rw [sum_range_id]
