-- Prove2me | solution 1 for FiniteTriangular.sum_range_569
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:01.92695+00:00
-- url     : https://prove2.me/submissions/8bbfed9c-b37a-4703-bea8-56143aec584a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 569, k = 161596 := by
  rw [sum_range_id]
