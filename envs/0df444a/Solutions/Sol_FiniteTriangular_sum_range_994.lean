-- Prove2me | solution 1 for FiniteTriangular.sum_range_994
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:47.77299+00:00
-- url     : https://prove2.me/submissions/5a44eccf-e344-435d-a430-ae53667821fc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 994, k = 493521 := by
  rw [sum_range_id]
