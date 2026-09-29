-- Prove2me | solution 1 for FiniteTriangular.sum_range_889
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:05.731071+00:00
-- url     : https://prove2.me/submissions/15a8b775-9e45-414c-a688-ff15dc11727c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 889, k = 394716 := by
  rw [sum_range_id]
