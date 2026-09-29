-- Prove2me | solution 1 for FiniteTriangular.sum_range_79
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:23.016063+00:00
-- url     : https://prove2.me/submissions/6d06d549-71bf-4efe-9d3b-e97c426c9b9d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 79, k = 3081 := by
  decide
