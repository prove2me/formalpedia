-- Prove2me | solution 1 for FiniteTriangular.sum_range_811
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:06.631219+00:00
-- url     : https://prove2.me/submissions/573f36c2-78a6-4334-83d6-700b4b4932ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 811, k = 328455 := by
  rw [sum_range_id]
