-- Prove2me | solution 1 for FiniteTriangular.sum_range_977
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:09.924691+00:00
-- url     : https://prove2.me/submissions/d64d3e69-13b2-4921-90e1-6b8ee81405ed

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 977, k = 476776 := by
  rw [sum_range_id]
