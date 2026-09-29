-- Prove2me | solution 1 for FiniteTriangular.sum_range_748
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:32.447329+00:00
-- url     : https://prove2.me/submissions/40d05961-e280-4c24-8fc7-126d7e805f5f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 748, k = 279378 := by
  rw [sum_range_id]
