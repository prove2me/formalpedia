-- Prove2me | solution 1 for FiniteTriangular.sum_range_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:05.134984+00:00
-- url     : https://prove2.me/submissions/c494652f-0308-4135-80ba-fdd2aa0653cc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 2, k = 1 := by
  decide
