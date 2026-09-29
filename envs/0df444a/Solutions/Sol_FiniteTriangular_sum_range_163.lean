-- Prove2me | solution 1 for FiniteTriangular.sum_range_163
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:16.347526+00:00
-- url     : https://prove2.me/submissions/49c03a93-385a-4403-ba51-75bf28eabb3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 163, k = 13203 := by
  rw [sum_range_id]
