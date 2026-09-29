-- Prove2me | solution 1 for FiniteTriangular.sum_range_390
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:09.302979+00:00
-- url     : https://prove2.me/submissions/22b05c6e-fd38-47cd-a052-1d1540da044f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 390, k = 75855 := by
  rw [sum_range_id]
