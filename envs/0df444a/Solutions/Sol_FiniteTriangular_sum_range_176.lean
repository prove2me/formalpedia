-- Prove2me | solution 1 for FiniteTriangular.sum_range_176
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:19.386104+00:00
-- url     : https://prove2.me/submissions/4cc2f7e2-63f0-447c-89f3-9e8d0e983b27

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 176, k = 15400 := by
  rw [sum_range_id]
