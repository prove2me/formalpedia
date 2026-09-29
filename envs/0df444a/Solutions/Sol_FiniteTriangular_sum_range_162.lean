-- Prove2me | solution 1 for FiniteTriangular.sum_range_162
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:15.74892+00:00
-- url     : https://prove2.me/submissions/30506851-e20d-4942-bc15-5502f4e53e96

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 162, k = 13041 := by
  rw [sum_range_id]
