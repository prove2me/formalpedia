-- Prove2me | solution 1 for FiniteTriangular.sum_range_823
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:57.353503+00:00
-- url     : https://prove2.me/submissions/b8a374bc-c00f-4c72-a332-327dec83afbc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 823, k = 338253 := by
  rw [sum_range_id]
