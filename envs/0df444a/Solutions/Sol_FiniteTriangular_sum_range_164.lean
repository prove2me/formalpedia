-- Prove2me | solution 1 for FiniteTriangular.sum_range_164
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:36.704688+00:00
-- url     : https://prove2.me/submissions/dde69be2-4e5f-40f7-86df-12642e2c6714

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 164, k = 13366 := by
  rw [sum_range_id]
