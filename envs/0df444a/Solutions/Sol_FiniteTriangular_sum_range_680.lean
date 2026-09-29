-- Prove2me | solution 1 for FiniteTriangular.sum_range_680
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:15.551595+00:00
-- url     : https://prove2.me/submissions/f2e2d3f0-84d7-4e62-b455-c76547999a04

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 680, k = 230860 := by
  rw [sum_range_id]
