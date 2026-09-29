-- Prove2me | solution 1 for FiniteTriangular.sum_range_701
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:12.033521+00:00
-- url     : https://prove2.me/submissions/ddaafa5e-ef1f-4570-8798-d20f7471a10d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 701, k = 245350 := by
  rw [sum_range_id]
