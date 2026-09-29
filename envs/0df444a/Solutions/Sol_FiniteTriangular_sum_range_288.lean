-- Prove2me | solution 1 for FiniteTriangular.sum_range_288
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:45.181275+00:00
-- url     : https://prove2.me/submissions/d69e3a8f-7ae7-4807-a6a0-b8f221c07769

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 288, k = 41328 := by
  rw [sum_range_id]
