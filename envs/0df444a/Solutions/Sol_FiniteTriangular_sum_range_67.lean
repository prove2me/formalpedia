-- Prove2me | solution 1 for FiniteTriangular.sum_range_67
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:02.517011+00:00
-- url     : https://prove2.me/submissions/e7ff5b23-4e6a-4539-b769-381a7d525a74

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 67, k = 2211 := by
  decide
