-- Prove2me | solution 1 for FiniteTriangular.sum_range_974
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:27.049494+00:00
-- url     : https://prove2.me/submissions/e69dd413-9081-4dc7-a579-fb824a386f89

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 974, k = 473851 := by
  rw [sum_range_id]
