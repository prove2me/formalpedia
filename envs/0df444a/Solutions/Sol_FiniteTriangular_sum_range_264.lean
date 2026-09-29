-- Prove2me | solution 1 for FiniteTriangular.sum_range_264
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:17.25402+00:00
-- url     : https://prove2.me/submissions/3ad1174c-52d6-410d-9937-65a31e349a67

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 264, k = 34716 := by
  rw [sum_range_id]
