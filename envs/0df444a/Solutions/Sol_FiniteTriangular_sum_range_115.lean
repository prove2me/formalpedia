-- Prove2me | solution 1 for FiniteTriangular.sum_range_115
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:18.524985+00:00
-- url     : https://prove2.me/submissions/c8a45bad-3ff2-4930-86eb-08872ab58873

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 115, k = 6555 := by
  decide
