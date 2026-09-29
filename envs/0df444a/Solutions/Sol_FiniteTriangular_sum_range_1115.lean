-- Prove2me | solution 1 for FiniteTriangular.sum_range_1115
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:06.79705+00:00
-- url     : https://prove2.me/submissions/2d9433de-08e9-4c0b-8b0e-cc97970c2c86

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1115, k = 621055 := by
  rw [sum_range_id]
