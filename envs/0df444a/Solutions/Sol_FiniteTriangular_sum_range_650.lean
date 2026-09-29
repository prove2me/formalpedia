-- Prove2me | solution 1 for FiniteTriangular.sum_range_650
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:01.634049+00:00
-- url     : https://prove2.me/submissions/2f5fa347-cd84-4601-84e5-921c613cb8d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 650, k = 210925 := by
  rw [sum_range_id]
