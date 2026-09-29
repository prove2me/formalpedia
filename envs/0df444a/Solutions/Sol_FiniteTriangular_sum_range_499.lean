-- Prove2me | solution 1 for FiniteTriangular.sum_range_499
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:34.670633+00:00
-- url     : https://prove2.me/submissions/292b3b33-81c3-49bb-bfec-2dfcd33b0d20

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 499, k = 124251 := by
  rw [sum_range_id]
