-- Prove2me | solution 1 for FiniteTriangular.sum_range_410
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:16.871405+00:00
-- url     : https://prove2.me/submissions/ca94c113-5cd0-4f27-8acf-a789883d70e5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 410, k = 83845 := by
  rw [sum_range_id]
