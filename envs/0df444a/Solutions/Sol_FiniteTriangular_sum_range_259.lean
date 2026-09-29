-- Prove2me | solution 1 for FiniteTriangular.sum_range_259
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:14.157796+00:00
-- url     : https://prove2.me/submissions/e11ac855-36be-47cf-a06a-a5bffb6e5e00

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 259, k = 33411 := by
  rw [sum_range_id]
