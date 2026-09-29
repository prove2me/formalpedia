-- Prove2me | solution 1 for FiniteTriangular.sum_range_688
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:05.287935+00:00
-- url     : https://prove2.me/submissions/5787bf64-c4ed-46e5-88be-05a2667f27af

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 688, k = 236328 := by
  rw [sum_range_id]
