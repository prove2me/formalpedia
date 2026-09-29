-- Prove2me | solution 1 for FiniteTriangular.sum_range_132
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:45.625044+00:00
-- url     : https://prove2.me/submissions/8b6141bb-99c6-4394-ac6c-8d8d23b248d2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 132, k = 8646 := by
  rw [sum_range_id]
