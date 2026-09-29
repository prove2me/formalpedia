-- Prove2me | solution 1 for FiniteTriangular.sum_range_1023
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:12.210974+00:00
-- url     : https://prove2.me/submissions/5441caa0-c499-4446-8628-7943cb312e50

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1023, k = 522753 := by
  rw [sum_range_id]
