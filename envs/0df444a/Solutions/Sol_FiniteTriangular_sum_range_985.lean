-- Prove2me | solution 1 for FiniteTriangular.sum_range_985
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:03.704738+00:00
-- url     : https://prove2.me/submissions/f2e67fb0-fa91-4ffa-86d6-d04f9551920d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 985, k = 484620 := by
  rw [sum_range_id]
