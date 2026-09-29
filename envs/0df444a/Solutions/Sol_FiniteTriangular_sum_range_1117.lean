-- Prove2me | solution 1 for FiniteTriangular.sum_range_1117
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:07.995733+00:00
-- url     : https://prove2.me/submissions/9e08a9af-b28b-423c-b0a7-84d5c8c995e1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1117, k = 623286 := by
  rw [sum_range_id]
