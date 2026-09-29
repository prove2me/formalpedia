-- Prove2me | solution 1 for FiniteTriangular.sum_range_1073
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:30.132608+00:00
-- url     : https://prove2.me/submissions/52385ab5-08c6-439e-9c26-7ce2f4fee110

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1073, k = 575128 := by
  rw [sum_range_id]
