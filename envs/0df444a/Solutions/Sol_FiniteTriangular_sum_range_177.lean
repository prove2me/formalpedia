-- Prove2me | solution 1 for FiniteTriangular.sum_range_177
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:20.443353+00:00
-- url     : https://prove2.me/submissions/e017e0bd-7fb4-4239-a5d1-458a0ed5a950

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 177, k = 15576 := by
  rw [sum_range_id]
