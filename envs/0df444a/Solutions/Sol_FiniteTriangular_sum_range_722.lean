-- Prove2me | solution 1 for FiniteTriangular.sum_range_722
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:10:57.836935+00:00
-- url     : https://prove2.me/submissions/d3b03364-acc2-4fd4-9ab4-b5c0256c6d5e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 722, k = 260281 := by
  rw [sum_range_id]
