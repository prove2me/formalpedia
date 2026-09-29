-- Prove2me | solution 1 for FiniteTriangular.sum_range_895
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:09.946965+00:00
-- url     : https://prove2.me/submissions/cdab99b9-73bd-409e-a54a-bae672cb6846

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 895, k = 400065 := by
  rw [sum_range_id]
