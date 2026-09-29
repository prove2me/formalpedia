-- Prove2me | solution 1 for FiniteTriangular.sum_range_112
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:28.125164+00:00
-- url     : https://prove2.me/submissions/9edd61c9-c886-4852-922e-269b8c489804

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 112, k = 6216 := by
  decide
