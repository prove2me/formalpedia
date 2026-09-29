-- Prove2me | solution 1 for FiniteTriangular.sum_range_299
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:05.502081+00:00
-- url     : https://prove2.me/submissions/1204d6b0-de6d-462f-850a-47a4c52bab6c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 299, k = 44551 := by
  rw [sum_range_id]
