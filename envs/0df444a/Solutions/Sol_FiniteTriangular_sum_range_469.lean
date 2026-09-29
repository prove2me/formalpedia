-- Prove2me | solution 1 for FiniteTriangular.sum_range_469
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:51.588131+00:00
-- url     : https://prove2.me/submissions/51dd9290-491b-431e-9c0e-d5fc4ceec5e2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 469, k = 109746 := by
  rw [sum_range_id]
