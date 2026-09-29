-- Prove2me | solution 1 for FiniteTriangular.sum_range_639
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:52.856983+00:00
-- url     : https://prove2.me/submissions/61b67ff8-d21b-474e-87b2-4b0eb081a815

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 639, k = 203841 := by
  rw [sum_range_id]
