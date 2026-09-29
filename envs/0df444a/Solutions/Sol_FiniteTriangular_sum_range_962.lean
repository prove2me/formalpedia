-- Prove2me | solution 1 for FiniteTriangular.sum_range_962
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:46.003388+00:00
-- url     : https://prove2.me/submissions/1c454fae-57ac-472f-9c81-5419ec454865

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 962, k = 462241 := by
  rw [sum_range_id]
