-- Prove2me | solution 1 for FiniteTriangular.sum_range_879
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:44.537924+00:00
-- url     : https://prove2.me/submissions/40bbfadb-c018-4ac3-9e70-a509f47bf550

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 879, k = 385881 := by
  rw [sum_range_id]
