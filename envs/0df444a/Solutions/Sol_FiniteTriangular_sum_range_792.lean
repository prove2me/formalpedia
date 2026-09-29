-- Prove2me | solution 1 for FiniteTriangular.sum_range_792
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:09.781917+00:00
-- url     : https://prove2.me/submissions/c7ffa471-f2d6-4693-a6d2-3a6fcc88334a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 792, k = 313236 := by
  rw [sum_range_id]
