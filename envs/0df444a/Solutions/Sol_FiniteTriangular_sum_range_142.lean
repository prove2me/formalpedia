-- Prove2me | solution 1 for FiniteTriangular.sum_range_142
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:19.83751+00:00
-- url     : https://prove2.me/submissions/1960cf70-694b-4aa2-8a61-defee6182258

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 142, k = 10011 := by
  rw [sum_range_id]
