-- Prove2me | solution 1 for FiniteTriangular.sum_range_543
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:08.970527+00:00
-- url     : https://prove2.me/submissions/cd6e8403-d91c-4108-9819-7faff55435a1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 543, k = 147153 := by
  rw [sum_range_id]
