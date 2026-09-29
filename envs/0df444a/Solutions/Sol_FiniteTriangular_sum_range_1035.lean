-- Prove2me | solution 1 for FiniteTriangular.sum_range_1035
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:56.07724+00:00
-- url     : https://prove2.me/submissions/b25727ad-acfd-423f-b207-1abc6f99bef1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1035, k = 535095 := by
  rw [sum_range_id]
