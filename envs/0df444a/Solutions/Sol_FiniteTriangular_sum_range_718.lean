-- Prove2me | solution 1 for FiniteTriangular.sum_range_718
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:53.98666+00:00
-- url     : https://prove2.me/submissions/bb9ea4db-0174-44f1-8dca-9ed8d63aaa3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 718, k = 257403 := by
  rw [sum_range_id]
