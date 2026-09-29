-- Prove2me | solution 1 for FiniteTriangular.sum_range_797
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:45.645652+00:00
-- url     : https://prove2.me/submissions/e74e68b7-9d29-49bf-bdde-1c9344c37022

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 797, k = 317206 := by
  rw [sum_range_id]
