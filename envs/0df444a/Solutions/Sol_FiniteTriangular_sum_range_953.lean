-- Prove2me | solution 1 for FiniteTriangular.sum_range_953
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:00:55.970767+00:00
-- url     : https://prove2.me/submissions/49a74d20-1895-4693-913e-be35c810d5a3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 953, k = 453628 := by
  rw [sum_range_id]
