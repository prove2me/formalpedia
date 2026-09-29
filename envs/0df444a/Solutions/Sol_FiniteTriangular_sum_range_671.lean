-- Prove2me | solution 1 for FiniteTriangular.sum_range_671
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:26.293837+00:00
-- url     : https://prove2.me/submissions/8fe08c7b-77a8-487a-a0ff-45ba9e49d506

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 671, k = 224785 := by
  rw [sum_range_id]
