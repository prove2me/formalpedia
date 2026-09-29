-- Prove2me | solution 1 for FiniteTriangular.sum_range_405
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:33.27014+00:00
-- url     : https://prove2.me/submissions/0f5289ef-d356-4ebb-bc67-144c4c6a5379

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 405, k = 81810 := by
  rw [sum_range_id]
