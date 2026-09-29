-- Prove2me | solution 1 for FiniteTriangular.sum_range_91
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:51.401306+00:00
-- url     : https://prove2.me/submissions/b72beb41-c6a0-44d9-9ac8-58cbe1328539

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 91, k = 4095 := by
  decide
