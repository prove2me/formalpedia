-- Prove2me | solution 1 for FiniteTriangular.sum_range_525
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:53.343806+00:00
-- url     : https://prove2.me/submissions/2f524205-3743-4d46-8351-c0d0c36b741b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 525, k = 137550 := by
  rw [sum_range_id]
