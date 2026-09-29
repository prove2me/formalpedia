-- Prove2me | solution 1 for FiniteTriangular.sum_range_954
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:00:56.731065+00:00
-- url     : https://prove2.me/submissions/ff46f8a1-3a4c-4c31-80dc-4d840d682d06

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 954, k = 454581 := by
  rw [sum_range_id]
