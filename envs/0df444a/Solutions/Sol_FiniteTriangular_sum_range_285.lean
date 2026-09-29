-- Prove2me | solution 1 for FiniteTriangular.sum_range_285
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:43.300275+00:00
-- url     : https://prove2.me/submissions/d538a2af-3e10-4327-97e9-9cd8f5dbb3c3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 285, k = 40470 := by
  rw [sum_range_id]
