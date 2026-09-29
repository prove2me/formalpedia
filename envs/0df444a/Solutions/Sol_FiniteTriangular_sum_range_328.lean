-- Prove2me | solution 1 for FiniteTriangular.sum_range_328
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:35.566226+00:00
-- url     : https://prove2.me/submissions/55ec5fcd-3005-48fa-86cb-fd93ab928046

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 328, k = 53628 := by
  rw [sum_range_id]
