-- Prove2me | solution 1 for FiniteTriangular.sum_range_406
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:33.942857+00:00
-- url     : https://prove2.me/submissions/1313bf50-fdee-4f7e-834c-0432b9af8140

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 406, k = 82215 := by
  rw [sum_range_id]
