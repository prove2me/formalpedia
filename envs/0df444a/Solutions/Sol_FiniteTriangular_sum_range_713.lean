-- Prove2me | solution 1 for FiniteTriangular.sum_range_713
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:50.925673+00:00
-- url     : https://prove2.me/submissions/b5b912d2-e746-49c2-af3f-075e6873b8a6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 713, k = 253828 := by
  rw [sum_range_id]
