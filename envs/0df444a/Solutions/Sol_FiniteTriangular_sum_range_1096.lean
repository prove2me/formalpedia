-- Prove2me | solution 1 for FiniteTriangular.sum_range_1096
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:24:03.008509+00:00
-- url     : https://prove2.me/submissions/fb59d42d-4647-4c87-92d3-b9e2b117ce05

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1096, k = 600060 := by
  rw [sum_range_id]
