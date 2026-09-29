-- Prove2me | solution 1 for FiniteTriangular.sum_range_738
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:42.656632+00:00
-- url     : https://prove2.me/submissions/06ab31e0-317f-447a-b843-24de3e108980

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 738, k = 271953 := by
  rw [sum_range_id]
