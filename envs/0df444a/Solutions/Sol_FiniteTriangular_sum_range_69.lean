-- Prove2me | solution 1 for FiniteTriangular.sum_range_69
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:04.232307+00:00
-- url     : https://prove2.me/submissions/fb575fb0-a61f-4571-88e4-8ea68b7d5af5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 69, k = 2346 := by
  decide
