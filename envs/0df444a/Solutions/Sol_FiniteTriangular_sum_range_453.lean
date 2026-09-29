-- Prove2me | solution 1 for FiniteTriangular.sum_range_453
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:02.169044+00:00
-- url     : https://prove2.me/submissions/cd82bc4c-6683-40d0-874d-7c8f21ebafa3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 453, k = 102378 := by
  rw [sum_range_id]
