-- Prove2me | solution 1 for FiniteTriangular.sum_range_158
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:13.033105+00:00
-- url     : https://prove2.me/submissions/3ff3e69b-6557-4403-a4a1-0bb2bc73c6fe

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 158, k = 12403 := by
  rw [sum_range_id]
