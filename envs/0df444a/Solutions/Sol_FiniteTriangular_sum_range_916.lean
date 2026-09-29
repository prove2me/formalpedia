-- Prove2me | solution 1 for FiniteTriangular.sum_range_916
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:51:59.855721+00:00
-- url     : https://prove2.me/submissions/98897332-41b6-4290-be2e-c0d1132a40e6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 916, k = 419070 := by
  rw [sum_range_id]
