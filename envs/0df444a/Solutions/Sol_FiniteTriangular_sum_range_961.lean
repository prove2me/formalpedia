-- Prove2me | solution 1 for FiniteTriangular.sum_range_961
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:44.977887+00:00
-- url     : https://prove2.me/submissions/60fed145-0d12-4738-808c-161f9752c099

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 961, k = 461280 := by
  rw [sum_range_id]
