-- Prove2me | solution 1 for FiniteTriangular.sum_range_786
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:06.225388+00:00
-- url     : https://prove2.me/submissions/ae7701e5-5742-4ada-9d88-7168b757e66c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 786, k = 308505 := by
  rw [sum_range_id]
