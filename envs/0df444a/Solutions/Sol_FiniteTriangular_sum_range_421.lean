-- Prove2me | solution 1 for FiniteTriangular.sum_range_421
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:04.805552+00:00
-- url     : https://prove2.me/submissions/a4f91680-a43f-4f38-a469-a95a7cc4e378

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 421, k = 88410 := by
  rw [sum_range_id]
