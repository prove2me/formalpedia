-- Prove2me | solution 1 for FiniteTriangular.sum_range_975
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:27.750197+00:00
-- url     : https://prove2.me/submissions/17b48781-bda1-4432-ba6c-3b1920ab8c1c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 975, k = 474825 := by
  rw [sum_range_id]
