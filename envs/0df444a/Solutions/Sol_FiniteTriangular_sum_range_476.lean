-- Prove2me | solution 1 for FiniteTriangular.sum_range_476
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:37.67086+00:00
-- url     : https://prove2.me/submissions/c5ad9741-01ec-4ed9-9e14-f0cdcced3fe7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 476, k = 113050 := by
  rw [sum_range_id]
