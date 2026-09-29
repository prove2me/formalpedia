-- Prove2me | solution 1 for FiniteTriangular.sum_range_523
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:52.083565+00:00
-- url     : https://prove2.me/submissions/1cadae88-3403-415c-a003-c598eea7261f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 523, k = 136503 := by
  rw [sum_range_id]
