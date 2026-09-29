-- Prove2me | solution 1 for FiniteTriangular.sum_range_425
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:48.8825+00:00
-- url     : https://prove2.me/submissions/7e9f79a3-0024-42e5-a013-9ea3637b51e9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 425, k = 90100 := by
  rw [sum_range_id]
