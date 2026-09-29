-- Prove2me | solution 1 for FiniteTriangular.sum_range_574
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:05.90606+00:00
-- url     : https://prove2.me/submissions/0f6875d1-93bc-4840-8247-39e9bc9659c5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 574, k = 164451 := by
  rw [sum_range_id]
