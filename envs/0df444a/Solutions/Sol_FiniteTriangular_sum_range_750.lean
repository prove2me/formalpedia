-- Prove2me | solution 1 for FiniteTriangular.sum_range_750
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:33.586915+00:00
-- url     : https://prove2.me/submissions/0708c7f9-c440-4422-9f90-d36e6f59f254

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 750, k = 280875 := by
  rw [sum_range_id]
