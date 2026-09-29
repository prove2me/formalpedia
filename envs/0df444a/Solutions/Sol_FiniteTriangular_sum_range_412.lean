-- Prove2me | solution 1 for FiniteTriangular.sum_range_412
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:18.168772+00:00
-- url     : https://prove2.me/submissions/d8d30d6b-ea99-4d1a-95c9-849f295cbd98

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 412, k = 84666 := by
  rw [sum_range_id]
