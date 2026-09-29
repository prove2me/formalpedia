-- Prove2me | solution 1 for FiniteTriangular.sum_range_675
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:12.227677+00:00
-- url     : https://prove2.me/submissions/5ea772cd-d791-4060-be0c-a172ced7dd70

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 675, k = 227475 := by
  rw [sum_range_id]
