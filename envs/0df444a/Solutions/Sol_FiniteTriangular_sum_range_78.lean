-- Prove2me | solution 1 for FiniteTriangular.sum_range_78
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:22.301364+00:00
-- url     : https://prove2.me/submissions/e3ec1871-341c-45ee-b979-8a17c68f7046

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 78, k = 3003 := by
  decide
