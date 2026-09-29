-- Prove2me | solution 1 for FiniteTriangular.sum_range_952
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:10.892136+00:00
-- url     : https://prove2.me/submissions/1ab14b38-8faf-41c0-a7bf-d4de7db54cca

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 952, k = 452676 := by
  rw [sum_range_id]
