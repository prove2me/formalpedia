-- Prove2me | solution 1 for FiniteTriangular.sum_range_503
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:37.148763+00:00
-- url     : https://prove2.me/submissions/06832fe9-2dc8-40ff-b9d2-34d94437bc99

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 503, k = 126253 := by
  rw [sum_range_id]
