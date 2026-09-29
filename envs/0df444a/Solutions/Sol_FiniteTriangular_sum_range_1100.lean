-- Prove2me | solution 1 for FiniteTriangular.sum_range_1100
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:42.181184+00:00
-- url     : https://prove2.me/submissions/3d540cf0-50b8-4b06-926e-c574199e34b1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1100, k = 604450 := by
  rw [sum_range_id]
