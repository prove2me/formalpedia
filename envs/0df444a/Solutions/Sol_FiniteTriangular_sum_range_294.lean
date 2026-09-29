-- Prove2me | solution 1 for FiniteTriangular.sum_range_294
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:20.405068+00:00
-- url     : https://prove2.me/submissions/b7665cbb-96d5-4154-a1af-4f56e2ef690c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 294, k = 43071 := by
  rw [sum_range_id]
