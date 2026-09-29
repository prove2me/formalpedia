-- Prove2me | solution 1 for FiniteTriangular.sum_range_946
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:07.201053+00:00
-- url     : https://prove2.me/submissions/7191cf3b-cfc6-4a29-bee4-00ceb30fe19d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 946, k = 446985 := by
  rw [sum_range_id]
