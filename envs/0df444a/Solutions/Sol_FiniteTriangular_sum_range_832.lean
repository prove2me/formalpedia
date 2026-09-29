-- Prove2me | solution 1 for FiniteTriangular.sum_range_832
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:45.640641+00:00
-- url     : https://prove2.me/submissions/314bac5c-f3da-4a22-94d4-6401c1ebb10d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 832, k = 345696 := by
  rw [sum_range_id]
