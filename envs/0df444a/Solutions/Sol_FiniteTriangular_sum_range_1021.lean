-- Prove2me | solution 1 for FiniteTriangular.sum_range_1021
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:10.902991+00:00
-- url     : https://prove2.me/submissions/512c57c5-c110-4270-9e06-22c7933d77c9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1021, k = 520710 := by
  rw [sum_range_id]
