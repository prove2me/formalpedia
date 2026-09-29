-- Prove2me | solution 1 for FiniteTriangular.sum_range_134
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:47.006805+00:00
-- url     : https://prove2.me/submissions/9e1d47e6-012d-4d47-89c1-58677b36d8bc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 134, k = 8911 := by
  rw [sum_range_id]
