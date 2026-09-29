-- Prove2me | solution 1 for FiniteTriangular.sum_range_101
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:37.535635+00:00
-- url     : https://prove2.me/submissions/d1b723a5-b3ee-4b3e-a81a-c5e31778cbbf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 101, k = 5050 := by
  decide
