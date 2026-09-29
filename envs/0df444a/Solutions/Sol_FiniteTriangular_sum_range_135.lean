-- Prove2me | solution 1 for FiniteTriangular.sum_range_135
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:47.684614+00:00
-- url     : https://prove2.me/submissions/21ce242b-7802-4419-aa7b-6be97833647d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 135, k = 9045 := by
  rw [sum_range_id]
