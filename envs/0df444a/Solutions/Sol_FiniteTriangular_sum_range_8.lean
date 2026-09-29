-- Prove2me | solution 1 for FiniteTriangular.sum_range_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:09.530981+00:00
-- url     : https://prove2.me/submissions/daf56078-d3ad-4c32-a79d-3b1f3c6afc70

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 8, k = 28 := by
  decide
