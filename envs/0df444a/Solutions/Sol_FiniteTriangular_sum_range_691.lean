-- Prove2me | solution 1 for FiniteTriangular.sum_range_691
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:37.986264+00:00
-- url     : https://prove2.me/submissions/67da38fc-8d61-45be-ae65-e9f80c5d7794

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 691, k = 238395 := by
  rw [sum_range_id]
