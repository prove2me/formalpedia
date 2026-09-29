-- Prove2me | solution 1 for FiniteTriangular.sum_range_189
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:19.391159+00:00
-- url     : https://prove2.me/submissions/13ec1b8e-4b99-4760-a079-65dcdbb41ac0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 189, k = 17766 := by
  rw [sum_range_id]
