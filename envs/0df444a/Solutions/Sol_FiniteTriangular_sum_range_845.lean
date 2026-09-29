-- Prove2me | solution 1 for FiniteTriangular.sum_range_845
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:57.814642+00:00
-- url     : https://prove2.me/submissions/5e1d8b0b-de7e-42a5-b112-25f3db9169e8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 845, k = 356590 := by
  rw [sum_range_id]
