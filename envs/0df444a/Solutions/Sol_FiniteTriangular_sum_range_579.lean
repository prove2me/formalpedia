-- Prove2me | solution 1 for FiniteTriangular.sum_range_579
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:48.235437+00:00
-- url     : https://prove2.me/submissions/e45b818c-2876-4d39-ab07-cce7dbfcf876

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 579, k = 167331 := by
  rw [sum_range_id]
