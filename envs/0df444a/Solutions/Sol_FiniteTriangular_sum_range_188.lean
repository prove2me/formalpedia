-- Prove2me | solution 1 for FiniteTriangular.sum_range_188
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:18.578034+00:00
-- url     : https://prove2.me/submissions/e55616b2-feaa-4492-ade5-a1b2d44a6585

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 188, k = 17578 := by
  rw [sum_range_id]
