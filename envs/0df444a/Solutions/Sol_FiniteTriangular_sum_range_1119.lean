-- Prove2me | solution 1 for FiniteTriangular.sum_range_1119
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:09.142073+00:00
-- url     : https://prove2.me/submissions/a2f9fe50-3916-450a-8f97-919a719e0a4d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1119, k = 625521 := by
  rw [sum_range_id]
