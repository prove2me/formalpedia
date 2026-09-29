-- Prove2me | solution 1 for FiniteTriangular.sum_range_477
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:38.277544+00:00
-- url     : https://prove2.me/submissions/7eac48c3-fff5-417b-9e79-3ad717fb8be2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 477, k = 113526 := by
  rw [sum_range_id]
