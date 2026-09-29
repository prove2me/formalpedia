-- Prove2me | solution 1 for FiniteTriangular.sum_range_180
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:24:27.497714+00:00
-- url     : https://prove2.me/submissions/ffc24fab-754c-46a7-81f1-b2a6d930a68c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 180, k = 16110 := by
  rw [sum_range_id]
