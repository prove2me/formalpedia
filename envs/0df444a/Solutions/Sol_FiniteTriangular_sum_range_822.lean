-- Prove2me | solution 1 for FiniteTriangular.sum_range_822
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:56.731419+00:00
-- url     : https://prove2.me/submissions/b28e5ad2-0aed-4215-926b-fd0ccfbaed29

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 822, k = 337431 := by
  rw [sum_range_id]
