-- Prove2me | solution 1 for FiniteTriangular.sum_range_758
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:14.17114+00:00
-- url     : https://prove2.me/submissions/4a05e762-2fdb-4331-84c9-0cf84c1725ef

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 758, k = 286903 := by
  rw [sum_range_id]
