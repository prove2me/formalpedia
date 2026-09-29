-- Prove2me | solution 1 for FiniteTriangular.sum_range_352
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:53.697635+00:00
-- url     : https://prove2.me/submissions/bf7597c0-b380-4b06-b73b-e974887ae2fe

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 352, k = 61776 := by
  rw [sum_range_id]
