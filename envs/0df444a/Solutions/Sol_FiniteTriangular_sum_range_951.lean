-- Prove2me | solution 1 for FiniteTriangular.sum_range_951
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:10.295344+00:00
-- url     : https://prove2.me/submissions/308b037d-08fa-49bc-b0d7-0122fd6651be

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 951, k = 451725 := by
  rw [sum_range_id]
