-- Prove2me | solution 1 for FiniteTriangular.sum_range_663
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:50.495264+00:00
-- url     : https://prove2.me/submissions/acfe4d4e-4d03-4e12-8c2b-e1c570720d7e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 663, k = 219453 := by
  rw [sum_range_id]
