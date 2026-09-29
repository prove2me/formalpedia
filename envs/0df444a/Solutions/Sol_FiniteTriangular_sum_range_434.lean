-- Prove2me | solution 1 for FiniteTriangular.sum_range_434
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:34.943056+00:00
-- url     : https://prove2.me/submissions/6c3fec0c-6684-4271-88b6-864e28066a5e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 434, k = 93961 := by
  rw [sum_range_id]
