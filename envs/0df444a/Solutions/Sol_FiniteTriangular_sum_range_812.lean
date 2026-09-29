-- Prove2me | solution 1 for FiniteTriangular.sum_range_812
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:07.239146+00:00
-- url     : https://prove2.me/submissions/78a6051b-1245-44c1-95f8-7c47cd28466c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 812, k = 329266 := by
  rw [sum_range_id]
