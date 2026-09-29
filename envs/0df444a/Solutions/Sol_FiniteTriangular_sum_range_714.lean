-- Prove2me | solution 1 for FiniteTriangular.sum_range_714
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:51.624721+00:00
-- url     : https://prove2.me/submissions/d272159a-7cc1-490c-9df6-e008dc522c21

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 714, k = 254541 := by
  rw [sum_range_id]
