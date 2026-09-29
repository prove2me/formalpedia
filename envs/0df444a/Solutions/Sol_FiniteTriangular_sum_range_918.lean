-- Prove2me | solution 1 for FiniteTriangular.sum_range_918
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:52:01.057987+00:00
-- url     : https://prove2.me/submissions/0050acd1-b11f-455a-940f-dfa85cba464b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 918, k = 420903 := by
  rw [sum_range_id]
