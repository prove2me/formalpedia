-- Prove2me | solution 1 for FiniteTriangular.sum_range_368
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:25.709314+00:00
-- url     : https://prove2.me/submissions/367bc745-1122-4656-b400-de80aa94a747

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 368, k = 67528 := by
  rw [sum_range_id]
