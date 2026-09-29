-- Prove2me | solution 1 for FiniteTriangular.sum_range_83
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:14.261978+00:00
-- url     : https://prove2.me/submissions/a5bc4ed1-7319-4f57-9b2d-987beba577ae

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 83, k = 3403 := by
  decide
