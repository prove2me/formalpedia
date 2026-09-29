-- Prove2me | solution 1 for FiniteTriangular.sum_range_347
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:50.173889+00:00
-- url     : https://prove2.me/submissions/bcef5d29-2484-4275-9f55-42e32835da4d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 347, k = 60031 := by
  rw [sum_range_id]
