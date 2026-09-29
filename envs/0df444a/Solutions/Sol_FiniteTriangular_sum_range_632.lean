-- Prove2me | solution 1 for FiniteTriangular.sum_range_632
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:07.448762+00:00
-- url     : https://prove2.me/submissions/5967deb6-a3a7-4923-bbaf-9c0e02313057

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 632, k = 199396 := by
  rw [sum_range_id]
