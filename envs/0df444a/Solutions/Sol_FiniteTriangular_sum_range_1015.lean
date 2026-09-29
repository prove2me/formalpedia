-- Prove2me | solution 1 for FiniteTriangular.sum_range_1015
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:30.736984+00:00
-- url     : https://prove2.me/submissions/92d7c924-94c3-4992-b41d-18fc9a2cfebd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1015, k = 514605 := by
  rw [sum_range_id]
