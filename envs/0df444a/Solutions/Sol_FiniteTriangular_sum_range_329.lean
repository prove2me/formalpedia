-- Prove2me | solution 1 for FiniteTriangular.sum_range_329
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:16.84957+00:00
-- url     : https://prove2.me/submissions/fb938587-d260-421d-a151-c56f2e4428e0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 329, k = 53956 := by
  rw [sum_range_id]
