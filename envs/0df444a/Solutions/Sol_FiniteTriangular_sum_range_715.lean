-- Prove2me | solution 1 for FiniteTriangular.sum_range_715
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:52.239818+00:00
-- url     : https://prove2.me/submissions/741a0d85-8c3f-4b86-91fd-1a0841eb2d9e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 715, k = 255255 := by
  rw [sum_range_id]
