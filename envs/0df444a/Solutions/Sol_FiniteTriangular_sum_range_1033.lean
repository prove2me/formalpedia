-- Prove2me | solution 1 for FiniteTriangular.sum_range_1033
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:54.475256+00:00
-- url     : https://prove2.me/submissions/02cc8361-171e-4fd5-956a-225ad54501c1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1033, k = 533028 := by
  rw [sum_range_id]
