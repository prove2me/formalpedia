-- Prove2me | solution 1 for FiniteTriangular.sum_range_265
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:12:58.299816+00:00
-- url     : https://prove2.me/submissions/5d4de463-7d09-4670-bbc4-465ce8cfafa0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 265, k = 34980 := by
  rw [sum_range_id]
