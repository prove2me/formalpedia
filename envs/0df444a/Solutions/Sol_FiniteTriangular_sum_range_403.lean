-- Prove2me | solution 1 for FiniteTriangular.sum_range_403
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:31.977124+00:00
-- url     : https://prove2.me/submissions/f4c8af5a-296b-47eb-ad5e-aa61e2c69754

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 403, k = 81003 := by
  rw [sum_range_id]
