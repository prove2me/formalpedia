-- Prove2me | solution 1 for FiniteTriangular.sum_range_1070
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:49.745598+00:00
-- url     : https://prove2.me/submissions/2a8551ff-7714-444a-ac12-3f593e93aad5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1070, k = 571915 := by
  rw [sum_range_id]
