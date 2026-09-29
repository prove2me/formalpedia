-- Prove2me | solution 1 for FiniteTriangular.sum_range_552
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:31:00.039693+00:00
-- url     : https://prove2.me/submissions/af1778ac-717f-452e-896f-cc178940b253

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 552, k = 152076 := by
  rw [sum_range_id]
