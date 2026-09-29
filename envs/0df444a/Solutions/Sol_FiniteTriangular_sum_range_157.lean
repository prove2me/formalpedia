-- Prove2me | solution 1 for FiniteTriangular.sum_range_157
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:12.429376+00:00
-- url     : https://prove2.me/submissions/52f5d50c-0215-4e01-804a-d9e636e7979d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 157, k = 12246 := by
  rw [sum_range_id]
