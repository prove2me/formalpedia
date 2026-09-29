-- Prove2me | solution 1 for FiniteTriangular.sum_range_170
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:42.975829+00:00
-- url     : https://prove2.me/submissions/9f304238-22f7-4ac0-ba28-25d9f25ced25

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 170, k = 14365 := by
  rw [sum_range_id]
