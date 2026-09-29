-- Prove2me | solution 1 for FiniteTriangular.sum_range_509
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:22.012277+00:00
-- url     : https://prove2.me/submissions/6636a77d-5529-4577-b3eb-e28faf6ded06

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 509, k = 129286 := by
  rw [sum_range_id]
