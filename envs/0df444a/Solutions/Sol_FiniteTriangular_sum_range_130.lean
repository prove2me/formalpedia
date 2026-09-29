-- Prove2me | solution 1 for FiniteTriangular.sum_range_130
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:26.164133+00:00
-- url     : https://prove2.me/submissions/297b3ce6-47dd-47c2-b1ed-91d8c24f3c79

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 130, k = 8385 := by
  rw [sum_range_id]
