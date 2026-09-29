-- Prove2me | solution 1 for FiniteTriangular.sum_range_831
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:45.024492+00:00
-- url     : https://prove2.me/submissions/8737631b-e58a-474d-bae8-ec37e9145ea6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 831, k = 344865 := by
  rw [sum_range_id]
