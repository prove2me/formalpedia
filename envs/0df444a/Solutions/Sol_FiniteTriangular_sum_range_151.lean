-- Prove2me | solution 1 for FiniteTriangular.sum_range_151
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:45.490436+00:00
-- url     : https://prove2.me/submissions/8b0b0ad3-dc2d-4d8a-a997-92de5dab7926

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 151, k = 11325 := by
  rw [sum_range_id]
