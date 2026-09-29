-- Prove2me | solution 1 for FiniteTriangular.sum_range_736
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:48.038352+00:00
-- url     : https://prove2.me/submissions/237f1d79-d21f-4e5f-87fc-382759a73e09

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 736, k = 270480 := by
  rw [sum_range_id]
