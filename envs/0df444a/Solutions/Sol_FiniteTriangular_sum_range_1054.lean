-- Prove2me | solution 1 for FiniteTriangular.sum_range_1054
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:15:02.935991+00:00
-- url     : https://prove2.me/submissions/28819728-db51-4d95-b2e0-5c643820d315

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1054, k = 554931 := by
  rw [sum_range_id]
