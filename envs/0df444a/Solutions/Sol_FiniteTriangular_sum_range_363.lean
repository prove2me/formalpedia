-- Prove2me | solution 1 for FiniteTriangular.sum_range_363
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:22.658977+00:00
-- url     : https://prove2.me/submissions/35e0e37a-f823-4a05-969f-16c3377cf1e4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 363, k = 65703 := by
  rw [sum_range_id]
