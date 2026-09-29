-- Prove2me | solution 1 for FiniteTriangular.sum_range_196
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:33.512979+00:00
-- url     : https://prove2.me/submissions/77f8a049-19eb-4e44-88e6-2e4e6da83933

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 196, k = 19110 := by
  rw [sum_range_id]
