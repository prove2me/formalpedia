-- Prove2me | solution 1 for FiniteTriangular.sum_range_545
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:54.900022+00:00
-- url     : https://prove2.me/submissions/3315105e-5b12-4c79-b9e3-978f7017ebcd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 545, k = 148240 := by
  rw [sum_range_id]
