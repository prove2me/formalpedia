-- Prove2me | solution 1 for FiniteTriangular.sum_range_464
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:06.569552+00:00
-- url     : https://prove2.me/submissions/332a3476-e206-46ef-a4d7-cab0a1b99078

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 464, k = 107416 := by
  rw [sum_range_id]
