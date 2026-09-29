-- Prove2me | solution 1 for FiniteTriangular.sum_range_539
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:06.644232+00:00
-- url     : https://prove2.me/submissions/ecd7d0e9-3207-40c3-a877-3df177973829

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 539, k = 144991 := by
  rw [sum_range_id]
