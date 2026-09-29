-- Prove2me | solution 1 for FiniteTriangular.sum_range_907
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:21.732935+00:00
-- url     : https://prove2.me/submissions/d4bb0c6b-26ed-4ea5-ba33-bb9ab14b706a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 907, k = 410871 := by
  rw [sum_range_id]
