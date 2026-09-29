-- Prove2me | solution 1 for FiniteTriangular.sum_range_519
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:08.565162+00:00
-- url     : https://prove2.me/submissions/12ec6d02-3a04-4d35-a306-e003b42026b1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 519, k = 134421 := by
  rw [sum_range_id]
