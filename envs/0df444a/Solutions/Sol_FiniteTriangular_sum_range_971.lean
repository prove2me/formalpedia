-- Prove2me | solution 1 for FiniteTriangular.sum_range_971
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:24.978599+00:00
-- url     : https://prove2.me/submissions/5fad8014-9ea9-4c0f-acda-acf98e6b712b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 971, k = 470935 := by
  rw [sum_range_id]
