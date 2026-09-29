-- Prove2me | solution 1 for FiniteTriangular.sum_range_367
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:25.148604+00:00
-- url     : https://prove2.me/submissions/86376aca-9894-4cab-95ac-9f965ebe0a0d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 367, k = 67161 := by
  rw [sum_range_id]
