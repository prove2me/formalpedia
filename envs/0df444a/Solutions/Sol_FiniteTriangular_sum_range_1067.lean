-- Prove2me | solution 1 for FiniteTriangular.sum_range_1067
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:47.902386+00:00
-- url     : https://prove2.me/submissions/f3b1e62b-92ed-441e-a829-fc4489f7f649

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1067, k = 568711 := by
  rw [sum_range_id]
