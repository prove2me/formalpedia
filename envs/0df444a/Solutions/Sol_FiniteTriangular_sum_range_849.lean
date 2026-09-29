-- Prove2me | solution 1 for FiniteTriangular.sum_range_849
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:30.937552+00:00
-- url     : https://prove2.me/submissions/0e531982-cdc6-4174-afa2-e675b39a506e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 849, k = 359976 := by
  rw [sum_range_id]
