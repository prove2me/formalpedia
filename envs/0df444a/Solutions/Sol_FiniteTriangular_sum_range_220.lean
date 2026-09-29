-- Prove2me | solution 1 for FiniteTriangular.sum_range_220
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:27.274134+00:00
-- url     : https://prove2.me/submissions/26973424-a574-4d32-832b-1c7ff8c322bb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 220, k = 24090 := by
  rw [sum_range_id]
