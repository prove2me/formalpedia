-- Prove2me | solution 1 for FiniteTriangular.sum_range_1066
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:47.212574+00:00
-- url     : https://prove2.me/submissions/beffc686-30b9-4af6-86ae-6a154d02cf89

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1066, k = 567645 := by
  rw [sum_range_id]
