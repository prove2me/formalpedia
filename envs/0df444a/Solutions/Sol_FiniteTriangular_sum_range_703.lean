-- Prove2me | solution 1 for FiniteTriangular.sum_range_703
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:13.280452+00:00
-- url     : https://prove2.me/submissions/c0833d7c-3e04-4ac5-a64d-6fe7418cad83

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 703, k = 246753 := by
  rw [sum_range_id]
