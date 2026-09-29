-- Prove2me | solution 1 for FiniteTriangular.sum_range_27
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:14.672401+00:00
-- url     : https://prove2.me/submissions/57f0a914-a9c6-45c8-aa97-0b3fdf0ab6ad

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 27, k = 351 := by
  decide
