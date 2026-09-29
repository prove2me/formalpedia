-- Prove2me | solution 1 for FiniteTriangular.sum_range_673
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:08.761092+00:00
-- url     : https://prove2.me/submissions/82ab4104-a8ac-495e-952e-777eaaad9749

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 673, k = 226128 := by
  rw [sum_range_id]
