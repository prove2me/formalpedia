-- Prove2me | solution 1 for FiniteTriangular.sum_range_1126
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:44.176733+00:00
-- url     : https://prove2.me/submissions/45c17a81-b0c2-4d62-a69b-b2d1695e52f9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1126, k = 633375 := by
  rw [sum_range_id]
