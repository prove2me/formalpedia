-- Prove2me | solution 1 for FiniteTriangular.sum_range_740
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:43.886382+00:00
-- url     : https://prove2.me/submissions/76820810-eca2-4427-a8bd-58cb1c0945c7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 740, k = 273430 := by
  rw [sum_range_id]
