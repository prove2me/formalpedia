-- Prove2me | solution 1 for FiniteTriangular.sum_range_118
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:21.49374+00:00
-- url     : https://prove2.me/submissions/425a8b2b-ca2d-4be3-a3fc-732d4d785000

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 118, k = 6903 := by
  decide
