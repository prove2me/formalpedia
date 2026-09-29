-- Prove2me | solution 1 for FiniteTriangular.sum_range_559
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:28.104504+00:00
-- url     : https://prove2.me/submissions/5757b070-7366-4f56-a4fa-3d7e177f09d9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 559, k = 155961 := by
  rw [sum_range_id]
