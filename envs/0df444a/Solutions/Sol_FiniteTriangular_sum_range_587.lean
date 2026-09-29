-- Prove2me | solution 1 for FiniteTriangular.sum_range_587
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:33.784152+00:00
-- url     : https://prove2.me/submissions/429f1427-35d5-4a9d-9d2a-4eb99df1038b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 587, k = 171991 := by
  rw [sum_range_id]
