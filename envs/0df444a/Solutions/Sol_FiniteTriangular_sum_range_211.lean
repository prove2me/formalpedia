-- Prove2me | solution 1 for FiniteTriangular.sum_range_211
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:42.457424+00:00
-- url     : https://prove2.me/submissions/bab1d781-0df0-448a-9ad7-8316c4f0703d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 211, k = 22155 := by
  rw [sum_range_id]
