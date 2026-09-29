-- Prove2me | solution 1 for FiniteTriangular.sum_range_686
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:04.052232+00:00
-- url     : https://prove2.me/submissions/7f20a30a-8b56-4e1c-84a6-62be22bcbda8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 686, k = 234955 := by
  rw [sum_range_id]
