-- Prove2me | solution 1 for FiniteTriangular.sum_range_719
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:54.60087+00:00
-- url     : https://prove2.me/submissions/79bc9659-a64e-4a3c-bdc5-1cd8e1166165

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 719, k = 258121 := by
  rw [sum_range_id]
