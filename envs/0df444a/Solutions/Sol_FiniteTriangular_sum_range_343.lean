-- Prove2me | solution 1 for FiniteTriangular.sum_range_343
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:07.429488+00:00
-- url     : https://prove2.me/submissions/1148bb36-eeb8-4cf8-8bbb-eca20f648d33

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 343, k = 58653 := by
  rw [sum_range_id]
