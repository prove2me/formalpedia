-- Prove2me | solution 1 for FiniteTriangular.sum_range_401
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:30.223344+00:00
-- url     : https://prove2.me/submissions/fbce0cfb-cac9-463a-8a4e-a20442a63000

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 401, k = 80200 := by
  rw [sum_range_id]
