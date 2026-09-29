-- Prove2me | solution 1 for FiniteTriangular.sum_range_273
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:52.367317+00:00
-- url     : https://prove2.me/submissions/c718325a-ad77-4c00-916e-4916f5ead07a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 273, k = 37128 := by
  rw [sum_range_id]
