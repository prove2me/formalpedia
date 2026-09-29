-- Prove2me | solution 1 for FiniteTriangular.sum_range_979
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:11.290769+00:00
-- url     : https://prove2.me/submissions/0a550992-626c-479f-b0ba-ca41661d61dc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 979, k = 478731 := by
  rw [sum_range_id]
