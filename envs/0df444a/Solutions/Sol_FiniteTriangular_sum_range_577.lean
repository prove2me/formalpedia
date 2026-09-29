-- Prove2me | solution 1 for FiniteTriangular.sum_range_577
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:47.051354+00:00
-- url     : https://prove2.me/submissions/5e74772c-b88f-46f8-a659-b7e70ea46fb7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 577, k = 166176 := by
  rw [sum_range_id]
