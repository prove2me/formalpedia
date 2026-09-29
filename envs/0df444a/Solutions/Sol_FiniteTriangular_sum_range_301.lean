-- Prove2me | solution 1 for FiniteTriangular.sum_range_301
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:06.77497+00:00
-- url     : https://prove2.me/submissions/4addcd72-624a-4a09-89bb-7fba34305a5a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 301, k = 45150 := by
  rw [sum_range_id]
