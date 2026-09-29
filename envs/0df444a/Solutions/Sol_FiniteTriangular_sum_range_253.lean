-- Prove2me | solution 1 for FiniteTriangular.sum_range_253
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:16.884904+00:00
-- url     : https://prove2.me/submissions/24778149-a756-4dfe-a5b5-8452db7b38b7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 253, k = 31878 := by
  rw [sum_range_id]
