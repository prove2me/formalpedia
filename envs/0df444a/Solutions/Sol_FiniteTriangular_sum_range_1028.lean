-- Prove2me | solution 1 for FiniteTriangular.sum_range_1028
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:56.127978+00:00
-- url     : https://prove2.me/submissions/0274b2a6-eaf0-45c9-8e0a-8cc085097bbf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1028, k = 527878 := by
  rw [sum_range_id]
