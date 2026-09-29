-- Prove2me | solution 1 for FiniteTriangular.sum_range_145
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:22.007896+00:00
-- url     : https://prove2.me/submissions/8bda78b6-28ae-4b41-9a0e-a56a6d8a26d9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 145, k = 10440 := by
  rw [sum_range_id]
