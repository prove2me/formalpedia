-- Prove2me | solution 1 for FiniteTriangular.sum_range_1043
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:18.080454+00:00
-- url     : https://prove2.me/submissions/5725cc04-86b1-40b7-989d-9ba06d55e610

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1043, k = 543403 := by
  rw [sum_range_id]
