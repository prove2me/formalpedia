-- Prove2me | solution 1 for FiniteTriangular.sum_range_986
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:04.332996+00:00
-- url     : https://prove2.me/submissions/67845dac-450f-46e8-9311-ec553a0c1e4c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 986, k = 485605 := by
  rw [sum_range_id]
