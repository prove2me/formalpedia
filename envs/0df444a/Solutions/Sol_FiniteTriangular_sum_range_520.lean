-- Prove2me | solution 1 for FiniteTriangular.sum_range_520
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:09.128451+00:00
-- url     : https://prove2.me/submissions/747589d2-4fc0-4cda-8ba0-dcede788ae4a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 520, k = 134940 := by
  rw [sum_range_id]
