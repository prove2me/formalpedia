-- Prove2me | solution 1 for FiniteTriangular.sum_range_62
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:37.801662+00:00
-- url     : https://prove2.me/submissions/23c38de3-5081-47d5-8171-2e17f76f3a75

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 62, k = 1891 := by
  decide
