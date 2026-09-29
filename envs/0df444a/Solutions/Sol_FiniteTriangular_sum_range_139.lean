-- Prove2me | solution 1 for FiniteTriangular.sum_range_139
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:50.323985+00:00
-- url     : https://prove2.me/submissions/15dcaaec-bcdc-4575-b36e-8ebee15fa654

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 139, k = 9591 := by
  rw [sum_range_id]
