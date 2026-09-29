-- Prove2me | solution 1 for FiniteTriangular.sum_range_734
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:46.828337+00:00
-- url     : https://prove2.me/submissions/8b5dd98d-ea0a-44fb-9a41-c9249b1c26b5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 734, k = 269011 := by
  rw [sum_range_id]
