-- Prove2me | solution 1 for FiniteTriangular.sum_range_431
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:53.345636+00:00
-- url     : https://prove2.me/submissions/a3c4bfaa-c94a-43a4-ab68-6842a0070987

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 431, k = 92665 := by
  rw [sum_range_id]
