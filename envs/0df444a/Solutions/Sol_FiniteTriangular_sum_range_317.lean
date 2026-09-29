-- Prove2me | solution 1 for FiniteTriangular.sum_range_317
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:36.855452+00:00
-- url     : https://prove2.me/submissions/24f2f273-fc20-4238-a74b-2974577d769f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 317, k = 50086 := by
  rw [sum_range_id]
