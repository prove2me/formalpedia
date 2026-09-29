-- Prove2me | solution 1 for FiniteTriangular.sum_range_394
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:53.061481+00:00
-- url     : https://prove2.me/submissions/5281278d-0d07-4fb2-bbe9-4afadd1a4e10

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 394, k = 77421 := by
  rw [sum_range_id]
