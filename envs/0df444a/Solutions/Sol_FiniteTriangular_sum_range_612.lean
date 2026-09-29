-- Prove2me | solution 1 for FiniteTriangular.sum_range_612
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:43.444574+00:00
-- url     : https://prove2.me/submissions/a611606a-b35a-41fc-85ca-1cf0d45bc303

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 612, k = 186966 := by
  rw [sum_range_id]
