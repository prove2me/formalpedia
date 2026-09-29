-- Prove2me | solution 1 for FiniteTriangular.sum_range_90
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:50.747155+00:00
-- url     : https://prove2.me/submissions/3a48e009-d2a7-4a39-a96b-712a3c290e74

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 90, k = 4005 := by
  decide
