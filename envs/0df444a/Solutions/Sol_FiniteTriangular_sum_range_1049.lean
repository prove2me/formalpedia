-- Prove2me | solution 1 for FiniteTriangular.sum_range_1049
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:14:59.026058+00:00
-- url     : https://prove2.me/submissions/af82fa6e-d347-4076-a2af-9f3e40c73867

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1049, k = 549676 := by
  rw [sum_range_id]
