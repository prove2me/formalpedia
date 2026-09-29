-- Prove2me | solution 1 for FiniteTriangular.sum_range_291
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:18.696386+00:00
-- url     : https://prove2.me/submissions/01c76f4a-94aa-492d-993e-c8dbc707e274

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 291, k = 42195 := by
  rw [sum_range_id]
