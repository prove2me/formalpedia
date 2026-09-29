-- Prove2me | solution 1 for FiniteTriangular.sum_range_1063
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:04.819177+00:00
-- url     : https://prove2.me/submissions/7e63dc15-f0e6-4c8b-98df-6497acc0a369

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1063, k = 564453 := by
  rw [sum_range_id]
