-- Prove2me | solution 1 for FiniteTriangular.sum_range_749
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:33.023688+00:00
-- url     : https://prove2.me/submissions/7b95452f-3e43-4c0a-8e5c-c185ec87e8dd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 749, k = 280126 := by
  rw [sum_range_id]
