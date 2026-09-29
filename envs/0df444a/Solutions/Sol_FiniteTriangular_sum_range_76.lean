-- Prove2me | solution 1 for FiniteTriangular.sum_range_76
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:20.913359+00:00
-- url     : https://prove2.me/submissions/a277ed5c-2d78-4195-86d0-60095c74e627

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 76, k = 2850 := by
  decide
