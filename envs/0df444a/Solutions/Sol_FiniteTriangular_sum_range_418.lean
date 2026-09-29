-- Prove2me | solution 1 for FiniteTriangular.sum_range_418
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:02.820086+00:00
-- url     : https://prove2.me/submissions/196fdaef-b375-4d79-a0a9-13ce56d34de3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 418, k = 87153 := by
  rw [sum_range_id]
