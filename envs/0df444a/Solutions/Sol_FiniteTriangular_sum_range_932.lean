-- Prove2me | solution 1 for FiniteTriangular.sum_range_932
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:33.824152+00:00
-- url     : https://prove2.me/submissions/03cdd12d-01ed-4db9-93a6-fc49e4d488c4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 932, k = 433846 := by
  rw [sum_range_id]
