-- Prove2me | solution 1 for FiniteTriangular.sum_range_875
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:41.938869+00:00
-- url     : https://prove2.me/submissions/83f4ab75-7fb9-4412-a2bb-2c590d80de58

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 875, k = 382375 := by
  rw [sum_range_id]
