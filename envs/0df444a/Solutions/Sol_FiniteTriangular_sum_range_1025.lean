-- Prove2me | solution 1 for FiniteTriangular.sum_range_1025
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:54.102178+00:00
-- url     : https://prove2.me/submissions/464b97c5-1fb5-44eb-8800-c96cb02fd42e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1025, k = 524800 := by
  rw [sum_range_id]
