-- Prove2me | solution 1 for FiniteTriangular.sum_range_581
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:49.368453+00:00
-- url     : https://prove2.me/submissions/76721159-1f8c-49cb-be36-cba38cb45ebb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 581, k = 168490 := by
  rw [sum_range_id]
