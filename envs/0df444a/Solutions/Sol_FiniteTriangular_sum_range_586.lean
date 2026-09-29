-- Prove2me | solution 1 for FiniteTriangular.sum_range_586
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:33.043311+00:00
-- url     : https://prove2.me/submissions/74ccfe4b-dce1-471a-a488-bc0360586a6d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 586, k = 171405 := by
  rw [sum_range_id]
