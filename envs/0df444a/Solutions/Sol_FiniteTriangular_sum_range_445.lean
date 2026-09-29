-- Prove2me | solution 1 for FiniteTriangular.sum_range_445
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:15.666717+00:00
-- url     : https://prove2.me/submissions/641f190e-b049-4308-86c2-f7502a160ff7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 445, k = 98790 := by
  rw [sum_range_id]
