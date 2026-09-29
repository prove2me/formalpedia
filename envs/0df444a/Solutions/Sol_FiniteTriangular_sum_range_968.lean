-- Prove2me | solution 1 for FiniteTriangular.sum_range_968
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:50.511146+00:00
-- url     : https://prove2.me/submissions/bd32af16-b13f-49c4-b27d-cc694674be91

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 968, k = 468028 := by
  rw [sum_range_id]
