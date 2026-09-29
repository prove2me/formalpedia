-- Prove2me | solution 1 for FiniteTriangular.sum_range_928
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:49.182664+00:00
-- url     : https://prove2.me/submissions/58ef9c4e-97b6-4ec4-8de1-1c0e07d30061

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 928, k = 430128 := by
  rw [sum_range_id]
