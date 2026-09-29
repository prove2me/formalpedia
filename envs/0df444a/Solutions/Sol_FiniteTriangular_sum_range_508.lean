-- Prove2me | solution 1 for FiniteTriangular.sum_range_508
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:21.368586+00:00
-- url     : https://prove2.me/submissions/60b4c39d-7918-4545-af6c-bf61ce0aff7e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 508, k = 128778 := by
  rw [sum_range_id]
