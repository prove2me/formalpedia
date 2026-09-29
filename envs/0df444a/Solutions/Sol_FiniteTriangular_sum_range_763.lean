-- Prove2me | solution 1 for FiniteTriangular.sum_range_763
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:49.945594+00:00
-- url     : https://prove2.me/submissions/2eaecb0c-5476-435c-aba5-8626905b7d61

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 763, k = 290703 := by
  rw [sum_range_id]
