-- Prove2me | solution 1 for FiniteTriangular.sum_range_186
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:16.318073+00:00
-- url     : https://prove2.me/submissions/97246272-773f-4b4d-b070-55cfdc6d34ce

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 186, k = 17205 := by
  rw [sum_range_id]
