-- Prove2me | solution 1 for FiniteTriangular.sum_range_344
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:08.058602+00:00
-- url     : https://prove2.me/submissions/12d1372d-fc6d-4786-aee5-07cb378783c6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 344, k = 58996 := by
  rw [sum_range_id]
