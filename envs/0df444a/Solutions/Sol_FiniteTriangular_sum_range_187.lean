-- Prove2me | solution 1 for FiniteTriangular.sum_range_187
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:17.093636+00:00
-- url     : https://prove2.me/submissions/a0714a2b-af42-4486-bfb9-c2f6ac424828

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 187, k = 17391 := by
  rw [sum_range_id]
