-- Prove2me | solution 1 for FiniteTriangular.sum_range_657
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:46.835589+00:00
-- url     : https://prove2.me/submissions/9a8d2a1c-b0ea-430d-ba03-9c336b50783b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 657, k = 215496 := by
  rw [sum_range_id]
