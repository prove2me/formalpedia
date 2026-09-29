-- Prove2me | solution 1 for FiniteTriangular.sum_range_901
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:45.345985+00:00
-- url     : https://prove2.me/submissions/b168c456-8966-45bc-8d33-ec361a8d7b52

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 901, k = 405450 := by
  rw [sum_range_id]
