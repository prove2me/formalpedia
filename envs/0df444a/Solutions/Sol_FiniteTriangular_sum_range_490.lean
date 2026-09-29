-- Prove2me | solution 1 for FiniteTriangular.sum_range_490
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:18:57.505627+00:00
-- url     : https://prove2.me/submissions/27b9a387-1a6b-4cbc-a0d8-857802753d87

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 490, k = 119805 := by
  rw [sum_range_id]
