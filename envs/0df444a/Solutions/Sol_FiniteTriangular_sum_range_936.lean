-- Prove2me | solution 1 for FiniteTriangular.sum_range_936
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:36.193497+00:00
-- url     : https://prove2.me/submissions/82041ac6-9feb-4774-8958-0ace3c307a98

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 936, k = 437580 := by
  rw [sum_range_id]
