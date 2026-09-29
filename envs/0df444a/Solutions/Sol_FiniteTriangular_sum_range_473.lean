-- Prove2me | solution 1 for FiniteTriangular.sum_range_473
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:35.818881+00:00
-- url     : https://prove2.me/submissions/3469da52-7cbe-4ab5-9ebc-109c793bf701

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 473, k = 111628 := by
  rw [sum_range_id]
