-- Prove2me | solution 1 for FiniteTriangular.sum_range_1078
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:33.445482+00:00
-- url     : https://prove2.me/submissions/f2b1171e-190a-4182-8b20-a71acb96efd0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1078, k = 580503 := by
  rw [sum_range_id]
