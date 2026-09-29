-- Prove2me | solution 1 for FiniteTriangular.sum_range_729
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:43.571316+00:00
-- url     : https://prove2.me/submissions/e1a6533c-c7b0-4e80-992e-fe2ce0a19bfa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 729, k = 265356 := by
  rw [sum_range_id]
