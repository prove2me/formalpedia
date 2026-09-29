-- Prove2me | solution 1 for FiniteTriangular.sum_range_377
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:20.006501+00:00
-- url     : https://prove2.me/submissions/e306ac9a-4e5d-49e2-b85b-2216075394d5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 377, k = 70876 := by
  rw [sum_range_id]
