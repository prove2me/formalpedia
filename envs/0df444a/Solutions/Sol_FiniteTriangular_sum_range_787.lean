-- Prove2me | solution 1 for FiniteTriangular.sum_range_787
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:06.838824+00:00
-- url     : https://prove2.me/submissions/b9801493-ca1d-4d11-bcce-c0326050e018

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 787, k = 309291 := by
  rw [sum_range_id]
