-- Prove2me | solution 1 for FiniteTriangular.sum_range_955
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:00:59.461818+00:00
-- url     : https://prove2.me/submissions/7ebfa2d5-4304-463c-9cbc-467a71dd99a6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 955, k = 455535 := by
  rw [sum_range_id]
