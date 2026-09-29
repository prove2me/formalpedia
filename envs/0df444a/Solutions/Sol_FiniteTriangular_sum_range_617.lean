-- Prove2me | solution 1 for FiniteTriangular.sum_range_617
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:18.381024+00:00
-- url     : https://prove2.me/submissions/1c5cc732-3bce-4a60-8361-53a2d6b9f59c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 617, k = 190036 := by
  rw [sum_range_id]
