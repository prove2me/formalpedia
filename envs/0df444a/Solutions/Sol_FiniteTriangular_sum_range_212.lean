-- Prove2me | solution 1 for FiniteTriangular.sum_range_212
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:43.045741+00:00
-- url     : https://prove2.me/submissions/b90e7e00-4998-4a4c-b86b-322c9b9f0dfc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 212, k = 22366 := by
  rw [sum_range_id]
