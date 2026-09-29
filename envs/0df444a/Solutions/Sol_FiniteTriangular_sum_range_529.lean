-- Prove2me | solution 1 for FiniteTriangular.sum_range_529
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:27.94642+00:00
-- url     : https://prove2.me/submissions/10c5dd6f-7e7d-4411-99e9-6a520d175fd1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 529, k = 139656 := by
  rw [sum_range_id]
