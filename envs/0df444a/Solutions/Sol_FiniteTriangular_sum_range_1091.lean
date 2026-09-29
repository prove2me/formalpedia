-- Prove2me | solution 1 for FiniteTriangular.sum_range_1091
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:23:59.567859+00:00
-- url     : https://prove2.me/submissions/f4e14b6d-2cbd-4e5a-b4d3-59da0d6d9b3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1091, k = 594595 := by
  rw [sum_range_id]
