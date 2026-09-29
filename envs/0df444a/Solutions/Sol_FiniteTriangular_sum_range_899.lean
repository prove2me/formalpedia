-- Prove2me | solution 1 for FiniteTriangular.sum_range_899
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:43.990028+00:00
-- url     : https://prove2.me/submissions/09be61d6-4870-48e4-8230-b5c441250394

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 899, k = 403651 := by
  rw [sum_range_id]
