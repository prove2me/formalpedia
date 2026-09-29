-- Prove2me | solution 1 for FiniteTriangular.sum_range_637
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:51.704975+00:00
-- url     : https://prove2.me/submissions/7e3a6fdb-a7b9-4ffb-af99-2a7a36b7a7ca

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 637, k = 202566 := by
  rw [sum_range_id]
