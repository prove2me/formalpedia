-- Prove2me | solution 1 for FiniteTriangular.sum_range_447
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:16.937758+00:00
-- url     : https://prove2.me/submissions/5d8522d2-353b-4160-ac43-026786f918c1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 447, k = 99681 := by
  rw [sum_range_id]
