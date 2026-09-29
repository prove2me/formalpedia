-- Prove2me | solution 1 for FiniteTriangular.sum_range_94
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:53.350516+00:00
-- url     : https://prove2.me/submissions/e4fa7ec6-66fe-49fe-a8af-cec6e0026803

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 94, k = 4371 := by
  decide
