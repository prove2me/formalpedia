-- Prove2me | solution 1 for FiniteTriangular.sum_range_234
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:44.035597+00:00
-- url     : https://prove2.me/submissions/3e898c3c-9f41-4dae-b23d-9c869c2f91c2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 234, k = 27261 := by
  rw [sum_range_id]
