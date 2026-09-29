-- Prove2me | solution 1 for FiniteTriangular.sum_range_215
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:44.667647+00:00
-- url     : https://prove2.me/submissions/021e2ead-dc16-455b-b361-648f15e20bf3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 215, k = 23005 := by
  rw [sum_range_id]
