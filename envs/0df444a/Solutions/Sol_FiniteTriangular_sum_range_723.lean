-- Prove2me | solution 1 for FiniteTriangular.sum_range_723
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:10:58.592372+00:00
-- url     : https://prove2.me/submissions/bb3f705a-9008-4342-bbdc-fb91e117df8a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 723, k = 261003 := by
  rw [sum_range_id]
