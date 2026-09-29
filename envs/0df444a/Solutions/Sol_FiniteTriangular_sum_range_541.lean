-- Prove2me | solution 1 for FiniteTriangular.sum_range_541
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:07.777405+00:00
-- url     : https://prove2.me/submissions/9e306f4f-88ab-4a0d-bd44-1e49fe075151

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 541, k = 146070 := by
  rw [sum_range_id]
