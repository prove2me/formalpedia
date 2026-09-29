-- Prove2me | solution 1 for FiniteTriangular.sum_range_427
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:50.209903+00:00
-- url     : https://prove2.me/submissions/cfa513c8-783a-45a4-b7a8-c390a95bba1d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 427, k = 90951 := by
  rw [sum_range_id]
