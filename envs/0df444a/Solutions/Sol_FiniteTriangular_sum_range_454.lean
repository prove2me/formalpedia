-- Prove2me | solution 1 for FiniteTriangular.sum_range_454
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:03.438076+00:00
-- url     : https://prove2.me/submissions/e4587a81-6b85-4048-acf8-f55d2977e5a9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 454, k = 102831 := by
  rw [sum_range_id]
