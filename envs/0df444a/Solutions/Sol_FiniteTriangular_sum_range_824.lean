-- Prove2me | solution 1 for FiniteTriangular.sum_range_824
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:57.976113+00:00
-- url     : https://prove2.me/submissions/d03b9551-c767-4935-b613-73a7bf3eeff5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 824, k = 339076 := by
  rw [sum_range_id]
