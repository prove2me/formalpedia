-- Prove2me | solution 1 for FiniteTriangular.sum_range_1112
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:34.920539+00:00
-- url     : https://prove2.me/submissions/32b14faf-08d6-492b-8a8e-e112c0041936

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1112, k = 617716 := by
  rw [sum_range_id]
