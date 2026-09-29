-- Prove2me | solution 1 for FiniteTriangular.sum_range_387
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:07.416206+00:00
-- url     : https://prove2.me/submissions/7aea3132-1b20-49f8-9f04-87050317c211

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 387, k = 74691 := by
  rw [sum_range_id]
