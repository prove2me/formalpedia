-- Prove2me | solution 1 for FiniteTriangular.sum_range_625
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:02.675198+00:00
-- url     : https://prove2.me/submissions/b980f480-cdfc-4e04-810c-cbbc4a3941a4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 625, k = 195000 := by
  rw [sum_range_id]
