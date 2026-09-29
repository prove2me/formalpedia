-- Prove2me | solution 1 for FiniteTriangular.sum_range_99
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:33.440491+00:00
-- url     : https://prove2.me/submissions/9ceedf98-734f-4f9f-92b6-7768c5211d16

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 99, k = 4851 := by
  decide
