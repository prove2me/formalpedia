-- Prove2me | solution 1 for FiniteTriangular.sum_range_641
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:23.875804+00:00
-- url     : https://prove2.me/submissions/7989aab8-f54e-4b88-a8e8-b2d662e3d9d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 641, k = 205120 := by
  rw [sum_range_id]
