-- Prove2me | solution 1 for FiniteTriangular.sum_range_694
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:39.838524+00:00
-- url     : https://prove2.me/submissions/a1cf0f59-2d55-4404-a52c-b768fc631d7f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 694, k = 240471 := by
  rw [sum_range_id]
