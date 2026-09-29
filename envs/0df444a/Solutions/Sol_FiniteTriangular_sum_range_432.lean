-- Prove2me | solution 1 for FiniteTriangular.sum_range_432
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:53.932255+00:00
-- url     : https://prove2.me/submissions/fbe62a6a-829e-494a-9274-7a696d9a800c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 432, k = 93096 := by
  rw [sum_range_id]
