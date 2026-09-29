-- Prove2me | solution 1 for FiniteTriangular.sum_range_1051
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:15:00.221449+00:00
-- url     : https://prove2.me/submissions/7ecd342c-472f-4aac-ba83-24bc6d4eaf69

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1051, k = 551775 := by
  rw [sum_range_id]
