-- Prove2me | solution 1 for FiniteTriangular.sum_range_672
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:26.956918+00:00
-- url     : https://prove2.me/submissions/c3c71a8d-437a-4c9e-92fc-9f8ac38ff302

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 672, k = 225456 := by
  rw [sum_range_id]
