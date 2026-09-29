-- Prove2me | solution 1 for FiniteTriangular.sum_range_697
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:09.580246+00:00
-- url     : https://prove2.me/submissions/d63948ca-fc06-4c41-b981-044aad7307ae

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 697, k = 242556 := by
  rw [sum_range_id]
