-- Prove2me | solution 1 for FiniteTriangular.sum_range_805
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:29.389162+00:00
-- url     : https://prove2.me/submissions/2efe3566-2e42-418f-9294-220505ded4fe

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 805, k = 323610 := by
  rw [sum_range_id]
