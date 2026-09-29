-- Prove2me | solution 1 for FiniteTriangular.sum_range_208
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:31.321521+00:00
-- url     : https://prove2.me/submissions/f15bc199-5850-4fef-b646-214d6b0b1e38

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 208, k = 21528 := by
  rw [sum_range_id]
