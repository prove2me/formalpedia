-- Prove2me | solution 1 for FiniteTriangular.sum_range_442
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:13.607376+00:00
-- url     : https://prove2.me/submissions/acc0312e-fa3d-4429-9b23-8c3309078ae0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 442, k = 97461 := by
  rw [sum_range_id]
