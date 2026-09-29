-- Prove2me | solution 1 for FiniteTriangular.sum_range_800
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:47.601885+00:00
-- url     : https://prove2.me/submissions/81513689-bbad-4911-b224-b65c79f03337

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 800, k = 319600 := by
  rw [sum_range_id]
