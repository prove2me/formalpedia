-- Prove2me | solution 1 for FiniteTriangular.sum_range_959
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:01:03.534343+00:00
-- url     : https://prove2.me/submissions/ede1f37e-650c-48c0-9ec3-749ee79d6818

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 959, k = 459361 := by
  rw [sum_range_id]
