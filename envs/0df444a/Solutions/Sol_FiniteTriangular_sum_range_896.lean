-- Prove2me | solution 1 for FiniteTriangular.sum_range_896
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:10.558527+00:00
-- url     : https://prove2.me/submissions/344005c2-7fe3-4048-8b05-880799cd4392

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 896, k = 400960 := by
  rw [sum_range_id]
