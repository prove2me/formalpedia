-- Prove2me | solution 1 for FiniteTriangular.sum_range_466
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:49.625708+00:00
-- url     : https://prove2.me/submissions/cd6f1518-c6cc-40ef-bafd-b0424676f905

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 466, k = 108345 := by
  rw [sum_range_id]
