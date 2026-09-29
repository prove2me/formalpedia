-- Prove2me | solution 1 for FiniteTriangular.sum_range_781
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:24.227923+00:00
-- url     : https://prove2.me/submissions/387a412e-d7e2-4c32-bc9e-d813f15c609f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 781, k = 304590 := by
  rw [sum_range_id]
