-- Prove2me | solution 1 for FiniteTriangular.sum_range_353
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:26.445986+00:00
-- url     : https://prove2.me/submissions/b8bb9d04-ece8-4cfb-8d43-c83bdeb6ac77

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 353, k = 62128 := by
  rw [sum_range_id]
