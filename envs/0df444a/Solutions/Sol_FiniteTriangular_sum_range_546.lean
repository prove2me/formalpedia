-- Prove2me | solution 1 for FiniteTriangular.sum_range_546
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:55.775716+00:00
-- url     : https://prove2.me/submissions/bda04214-a40e-4be1-9611-04ba57189c28

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 546, k = 148785 := by
  rw [sum_range_id]
