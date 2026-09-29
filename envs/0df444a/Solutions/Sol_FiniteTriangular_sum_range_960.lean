-- Prove2me | solution 1 for FiniteTriangular.sum_range_960
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:01:04.34835+00:00
-- url     : https://prove2.me/submissions/ef33a7e4-548c-4a42-9b1f-893d4086751c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 960, k = 460320 := by
  rw [sum_range_id]
