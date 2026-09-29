-- Prove2me | solution 1 for FiniteTriangular.sum_range_969
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:23.731724+00:00
-- url     : https://prove2.me/submissions/841f2314-ea46-4b68-b044-227c4f4c95fe

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 969, k = 468996 := by
  rw [sum_range_id]
