-- Prove2me | solution 1 for FiniteTriangular.sum_range_892
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:07.983754+00:00
-- url     : https://prove2.me/submissions/6a4db22b-ca1d-4600-bf62-0c543e14878f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 892, k = 397386 := by
  rw [sum_range_id]
