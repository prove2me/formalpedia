-- Prove2me | solution 1 for FiniteTriangular.sum_range_972
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:25.607656+00:00
-- url     : https://prove2.me/submissions/6d6f814f-fb31-499c-b3b7-093d452b0ce7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 972, k = 471906 := by
  rw [sum_range_id]
