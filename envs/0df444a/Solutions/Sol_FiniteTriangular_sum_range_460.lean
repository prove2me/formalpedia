-- Prove2me | solution 1 for FiniteTriangular.sum_range_460
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:04.133949+00:00
-- url     : https://prove2.me/submissions/6d62718b-a6a8-4bd0-87f1-cad9fd6f5c57

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 460, k = 105570 := by
  rw [sum_range_id]
