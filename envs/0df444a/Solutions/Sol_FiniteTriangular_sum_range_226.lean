-- Prove2me | solution 1 for FiniteTriangular.sum_range_226
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:11.948952+00:00
-- url     : https://prove2.me/submissions/9a09194a-be19-4258-938f-c9a18449a13f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 226, k = 25425 := by
  rw [sum_range_id]
