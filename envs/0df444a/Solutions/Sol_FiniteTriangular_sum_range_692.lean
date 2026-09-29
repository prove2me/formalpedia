-- Prove2me | solution 1 for FiniteTriangular.sum_range_692
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:38.727995+00:00
-- url     : https://prove2.me/submissions/760e8245-1248-4dc9-8c06-2054a7d752c9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 692, k = 239086 := by
  rw [sum_range_id]
