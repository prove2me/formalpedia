-- Prove2me | solution 1 for FiniteTriangular.sum_range_564
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:18.782142+00:00
-- url     : https://prove2.me/submissions/ab652362-ccfa-4fdf-91b7-37af5b83823a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 564, k = 158766 := by
  rw [sum_range_id]
