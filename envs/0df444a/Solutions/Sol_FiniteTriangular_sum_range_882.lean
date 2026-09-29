-- Prove2me | solution 1 for FiniteTriangular.sum_range_882
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:17.738059+00:00
-- url     : https://prove2.me/submissions/d59bdfbd-dcc5-4a9a-b33f-92c8a4e5b4ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 882, k = 388521 := by
  rw [sum_range_id]
