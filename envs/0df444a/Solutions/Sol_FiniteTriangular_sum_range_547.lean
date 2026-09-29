-- Prove2me | solution 1 for FiniteTriangular.sum_range_547
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:56.558125+00:00
-- url     : https://prove2.me/submissions/3756e35b-6322-4b29-98d4-2a0f4720a5d1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 547, k = 149331 := by
  rw [sum_range_id]
