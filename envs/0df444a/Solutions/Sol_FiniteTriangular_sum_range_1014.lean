-- Prove2me | solution 1 for FiniteTriangular.sum_range_1014
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:30.094986+00:00
-- url     : https://prove2.me/submissions/e9e237d6-4a29-496b-ab64-6f5674e050f6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1014, k = 513591 := by
  rw [sum_range_id]
