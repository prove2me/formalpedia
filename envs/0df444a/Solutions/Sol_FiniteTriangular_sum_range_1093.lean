-- Prove2me | solution 1 for FiniteTriangular.sum_range_1093
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:24:01.079647+00:00
-- url     : https://prove2.me/submissions/c45cf04e-0ba5-49eb-896e-e541a7d57402

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1093, k = 596778 := by
  rw [sum_range_id]
