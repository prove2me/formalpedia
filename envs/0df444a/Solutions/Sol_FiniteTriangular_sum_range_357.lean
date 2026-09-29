-- Prove2me | solution 1 for FiniteTriangular.sum_range_357
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:28.975757+00:00
-- url     : https://prove2.me/submissions/f5e8a3ad-7436-4576-aa1a-2752a4f52054

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 357, k = 63546 := by
  rw [sum_range_id]
