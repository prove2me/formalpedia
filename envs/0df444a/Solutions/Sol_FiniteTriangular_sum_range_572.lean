-- Prove2me | solution 1 for FiniteTriangular.sum_range_572
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:04.673704+00:00
-- url     : https://prove2.me/submissions/dce6b739-e2e9-4d20-9bb0-4b02fc2032a4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 572, k = 163306 := by
  rw [sum_range_id]
