-- Prove2me | solution 1 for FiniteTriangular.sum_range_1079
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:34.058469+00:00
-- url     : https://prove2.me/submissions/5fcbd84a-10bf-46f5-9031-73cf403c5faf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1079, k = 581581 := by
  rw [sum_range_id]
