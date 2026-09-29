-- Prove2me | solution 1 for FiniteTriangular.sum_range_388
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:07.964577+00:00
-- url     : https://prove2.me/submissions/adca0759-fae9-4cbd-9b6f-9cce8be936f4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 388, k = 75078 := by
  rw [sum_range_id]
