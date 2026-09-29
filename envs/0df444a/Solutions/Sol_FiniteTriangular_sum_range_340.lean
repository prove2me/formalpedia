-- Prove2me | solution 1 for FiniteTriangular.sum_range_340
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:05.644501+00:00
-- url     : https://prove2.me/submissions/abe0d224-5cdb-4d83-994f-cd30514a2200

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 340, k = 57630 := by
  rw [sum_range_id]
