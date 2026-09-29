-- Prove2me | solution 1 for FiniteTriangular.sum_range_105
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:21.547457+00:00
-- url     : https://prove2.me/submissions/a832285a-3593-44c3-86d7-dfb1a0693d50

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 105, k = 5460 := by
  decide
