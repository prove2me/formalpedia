-- Prove2me | solution 1 for FiniteTriangular.sum_range_884
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:19.038291+00:00
-- url     : https://prove2.me/submissions/b1a8eb31-e63d-42bd-8d04-b35face0af26

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 884, k = 390286 := by
  rw [sum_range_id]
