-- Prove2me | solution 1 for FiniteTriangular.sum_range_146
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:22.9728+00:00
-- url     : https://prove2.me/submissions/dd862328-78f7-45c9-baef-3bde04e8ea7f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 146, k = 10585 := by
  rw [sum_range_id]
