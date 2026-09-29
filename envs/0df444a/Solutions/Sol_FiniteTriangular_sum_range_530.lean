-- Prove2me | solution 1 for FiniteTriangular.sum_range_530
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:28.784624+00:00
-- url     : https://prove2.me/submissions/f3c1b8ab-10e4-4677-b88c-12d6a5f81546

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 530, k = 140185 := by
  rw [sum_range_id]
