-- Prove2me | solution 1 for FiniteTriangular.sum_range_250
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:13.347859+00:00
-- url     : https://prove2.me/submissions/9630c090-0047-45c5-96eb-e65d4d1f8b4a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 250, k = 31125 := by
  rw [sum_range_id]
