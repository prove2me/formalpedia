-- Prove2me | solution 1 for FiniteTriangular.sum_range_844
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:57.215722+00:00
-- url     : https://prove2.me/submissions/51792fa4-e9e8-4bc5-a935-10c6b13db80c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 844, k = 355746 := by
  rw [sum_range_id]
