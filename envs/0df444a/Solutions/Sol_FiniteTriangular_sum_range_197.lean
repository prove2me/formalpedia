-- Prove2me | solution 1 for FiniteTriangular.sum_range_197
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:34.109499+00:00
-- url     : https://prove2.me/submissions/b04c0d45-1749-434a-af11-7cecf5ee840d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 197, k = 19306 := by
  rw [sum_range_id]
