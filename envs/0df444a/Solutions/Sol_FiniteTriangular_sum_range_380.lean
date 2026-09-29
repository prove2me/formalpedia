-- Prove2me | solution 1 for FiniteTriangular.sum_range_380
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:21.917967+00:00
-- url     : https://prove2.me/submissions/70575531-033d-4209-ac83-1b85056aa42a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 380, k = 72010 := by
  rw [sum_range_id]
