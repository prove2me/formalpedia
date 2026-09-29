-- Prove2me | solution 1 for FiniteTriangular.sum_range_716
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:52.818004+00:00
-- url     : https://prove2.me/submissions/0eed5fe9-324c-4d71-a0fe-17859aa9a9fa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 716, k = 255970 := by
  rw [sum_range_id]
