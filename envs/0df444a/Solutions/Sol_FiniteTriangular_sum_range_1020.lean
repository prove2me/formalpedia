-- Prove2me | solution 1 for FiniteTriangular.sum_range_1020
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:10.291223+00:00
-- url     : https://prove2.me/submissions/e698d903-d570-4d60-99f6-da245abc823f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1020, k = 519690 := by
  rw [sum_range_id]
