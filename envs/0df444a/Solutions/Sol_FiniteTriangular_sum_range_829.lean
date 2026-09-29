-- Prove2me | solution 1 for FiniteTriangular.sum_range_829
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:43.676991+00:00
-- url     : https://prove2.me/submissions/b7f379b3-8448-451c-886b-4c50effc0040

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 829, k = 343206 := by
  rw [sum_range_id]
