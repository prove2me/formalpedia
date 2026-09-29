-- Prove2me | solution 1 for FiniteTriangular.sum_range_369
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:15.327762+00:00
-- url     : https://prove2.me/submissions/4a6327d1-da5a-43ac-990b-67abd18a4f4a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 369, k = 67896 := by
  rw [sum_range_id]
