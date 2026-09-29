-- Prove2me | solution 1 for FiniteTriangular.sum_range_507
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:20.809253+00:00
-- url     : https://prove2.me/submissions/fb07bd18-4a51-47b2-984d-775d27ecc577

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 507, k = 128271 := by
  rw [sum_range_id]
