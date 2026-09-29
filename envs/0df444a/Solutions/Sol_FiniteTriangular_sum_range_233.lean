-- Prove2me | solution 1 for FiniteTriangular.sum_range_233
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:43.444152+00:00
-- url     : https://prove2.me/submissions/8380ed2f-5e34-4f29-908a-62d3e6b2ded1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 233, k = 27028 := by
  rw [sum_range_id]
