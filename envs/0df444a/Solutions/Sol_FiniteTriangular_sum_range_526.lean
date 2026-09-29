-- Prove2me | solution 1 for FiniteTriangular.sum_range_526
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:53.902773+00:00
-- url     : https://prove2.me/submissions/772b2125-7cb4-4f7f-8035-c8e0109ee71a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 526, k = 138075 := by
  rw [sum_range_id]
