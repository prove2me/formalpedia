-- Prove2me | solution 1 for FiniteTriangular.sum_range_1097
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:40.25845+00:00
-- url     : https://prove2.me/submissions/aa42d972-effe-4846-989a-5f422260f1b5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1097, k = 601156 := by
  rw [sum_range_id]
