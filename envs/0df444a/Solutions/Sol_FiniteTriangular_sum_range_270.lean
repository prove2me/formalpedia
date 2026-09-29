-- Prove2me | solution 1 for FiniteTriangular.sum_range_270
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:13:01.346659+00:00
-- url     : https://prove2.me/submissions/a9b7d436-2437-4d9a-8dde-f9ef7037c61d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 270, k = 36315 := by
  rw [sum_range_id]
