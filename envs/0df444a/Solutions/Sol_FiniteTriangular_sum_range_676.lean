-- Prove2me | solution 1 for FiniteTriangular.sum_range_676
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:12.992635+00:00
-- url     : https://prove2.me/submissions/d3aa1767-e47d-47df-8c62-9faf170a045f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 676, k = 228150 := by
  rw [sum_range_id]
