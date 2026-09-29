-- Prove2me | solution 1 for FiniteTriangular.sum_range_689
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:36.828486+00:00
-- url     : https://prove2.me/submissions/811492e9-f25b-43b2-bfed-47e3fa7d4ffd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 689, k = 237016 := by
  rw [sum_range_id]
