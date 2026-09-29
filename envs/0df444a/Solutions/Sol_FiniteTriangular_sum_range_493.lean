-- Prove2me | solution 1 for FiniteTriangular.sum_range_493
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:18:59.383169+00:00
-- url     : https://prove2.me/submissions/580aa787-97ce-4cbe-8d74-fad527df8bc4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 493, k = 121278 := by
  rw [sum_range_id]
