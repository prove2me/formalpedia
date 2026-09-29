-- Prove2me | solution 1 for FiniteTriangular.sum_range_705
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:06:56.251657+00:00
-- url     : https://prove2.me/submissions/dbc6ebd0-9781-4799-b780-a7b2533f8461

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 705, k = 248160 := by
  rw [sum_range_id]
