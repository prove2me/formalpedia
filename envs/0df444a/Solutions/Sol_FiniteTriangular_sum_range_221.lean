-- Prove2me | solution 1 for FiniteTriangular.sum_range_221
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:27.834349+00:00
-- url     : https://prove2.me/submissions/c14f01da-9e33-43f2-aa70-383ff4916da0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 221, k = 24310 := by
  rw [sum_range_id]
