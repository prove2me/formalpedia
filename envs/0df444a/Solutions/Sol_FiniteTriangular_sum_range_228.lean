-- Prove2me | solution 1 for FiniteTriangular.sum_range_228
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:13.084205+00:00
-- url     : https://prove2.me/submissions/e6211192-05d4-4608-b512-572647d7b1c5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 228, k = 25878 := by
  rw [sum_range_id]
