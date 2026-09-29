-- Prove2me | solution 1 for FiniteTriangular.sum_range_1130
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:32:22.040375+00:00
-- url     : https://prove2.me/submissions/3c54e181-74b9-49e6-aa56-93a689ef1db6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1130, k = 637885 := by
  rw [sum_range_id]
