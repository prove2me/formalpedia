-- Prove2me | solution 1 for FiniteTriangular.sum_range_583
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:50.548588+00:00
-- url     : https://prove2.me/submissions/2cb64af0-4bf3-4ae4-88ea-76752d5124f5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 583, k = 169653 := by
  rw [sum_range_id]
