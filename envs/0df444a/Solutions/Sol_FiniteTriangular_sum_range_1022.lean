-- Prove2me | solution 1 for FiniteTriangular.sum_range_1022
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:11.505325+00:00
-- url     : https://prove2.me/submissions/483972d2-7dab-4bbb-b2fe-1ed5ddad2c2c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1022, k = 521731 := by
  rw [sum_range_id]
