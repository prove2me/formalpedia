-- Prove2me | solution 1 for FiniteTriangular.sum_range_373
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:17.524467+00:00
-- url     : https://prove2.me/submissions/e14b7b48-e4e8-4e0e-8897-23f895f63304

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 373, k = 69378 := by
  rw [sum_range_id]
