-- Prove2me | solution 1 for FiniteTriangular.sum_range_122
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:54:14.773657+00:00
-- url     : https://prove2.me/submissions/4b183756-e3f0-4cdb-aa22-08948ca81c76

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 122, k = 7381 := by
  decide
