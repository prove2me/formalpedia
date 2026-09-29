-- Prove2me | solution 1 for FiniteTriangular.sum_range_728
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:11:01.791888+00:00
-- url     : https://prove2.me/submissions/369a7b76-6421-4b9c-9ee2-7f9665c090aa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 728, k = 264628 := by
  rw [sum_range_id]
