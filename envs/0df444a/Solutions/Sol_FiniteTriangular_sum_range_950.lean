-- Prove2me | solution 1 for FiniteTriangular.sum_range_950
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:09.665293+00:00
-- url     : https://prove2.me/submissions/90bffd07-026d-467d-aa26-f93df361e103

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 950, k = 450775 := by
  rw [sum_range_id]
