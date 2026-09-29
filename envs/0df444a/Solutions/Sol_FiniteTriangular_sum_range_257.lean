-- Prove2me | solution 1 for FiniteTriangular.sum_range_257
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:12.78798+00:00
-- url     : https://prove2.me/submissions/3d7de0e8-3a33-4940-bd41-dc99ffb9cff7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 257, k = 32896 := by
  rw [sum_range_id]
