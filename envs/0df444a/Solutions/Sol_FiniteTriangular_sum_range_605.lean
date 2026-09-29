-- Prove2me | solution 1 for FiniteTriangular.sum_range_605
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:55.73572+00:00
-- url     : https://prove2.me/submissions/627262d0-2d06-4bb7-9b17-dc18b2de3054

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 605, k = 182710 := by
  rw [sum_range_id]
