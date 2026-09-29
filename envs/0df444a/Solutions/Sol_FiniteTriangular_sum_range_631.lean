-- Prove2me | solution 1 for FiniteTriangular.sum_range_631
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:06.794659+00:00
-- url     : https://prove2.me/submissions/873abd07-8621-44c2-89cd-405392d08701

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 631, k = 198765 := by
  rw [sum_range_id]
