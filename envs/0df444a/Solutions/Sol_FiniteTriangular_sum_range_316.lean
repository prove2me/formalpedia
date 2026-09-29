-- Prove2me | solution 1 for FiniteTriangular.sum_range_316
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:36.266257+00:00
-- url     : https://prove2.me/submissions/ceb0573b-e599-448c-92ac-3913f9748769

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 316, k = 49770 := by
  rw [sum_range_id]
