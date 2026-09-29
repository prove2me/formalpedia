-- Prove2me | solution 1 for FiniteTriangular.sum_range_318
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:37.474639+00:00
-- url     : https://prove2.me/submissions/85bb013d-142f-42ee-8a13-d208d2f8a064

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 318, k = 50403 := by
  rw [sum_range_id]
