-- Prove2me | solution 1 for FiniteTriangular.sum_range_724
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:10:59.258435+00:00
-- url     : https://prove2.me/submissions/c69087dc-7f98-4ca4-b08b-cb38f2fde67a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 724, k = 261726 := by
  rw [sum_range_id]
