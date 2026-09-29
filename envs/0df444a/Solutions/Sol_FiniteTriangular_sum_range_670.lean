-- Prove2me | solution 1 for FiniteTriangular.sum_range_670
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:25.69064+00:00
-- url     : https://prove2.me/submissions/ab01c852-433b-428b-b923-af54846259c4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 670, k = 224115 := by
  rw [sum_range_id]
