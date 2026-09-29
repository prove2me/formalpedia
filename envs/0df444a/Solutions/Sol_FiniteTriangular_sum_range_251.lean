-- Prove2me | solution 1 for FiniteTriangular.sum_range_251
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:13.953577+00:00
-- url     : https://prove2.me/submissions/80d966e7-22db-4611-bafc-ca25830bbb81

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 251, k = 31375 := by
  rw [sum_range_id]
