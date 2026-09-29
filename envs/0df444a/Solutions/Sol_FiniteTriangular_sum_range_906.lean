-- Prove2me | solution 1 for FiniteTriangular.sum_range_906
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:21.051063+00:00
-- url     : https://prove2.me/submissions/b061d0be-b03a-4911-95ef-5ca9f76b3754

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 906, k = 409965 := by
  rw [sum_range_id]
