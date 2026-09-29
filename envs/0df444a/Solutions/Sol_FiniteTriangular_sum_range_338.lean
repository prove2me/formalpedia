-- Prove2me | solution 1 for FiniteTriangular.sum_range_338
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:04.125175+00:00
-- url     : https://prove2.me/submissions/f5b3688d-2c89-44ef-8aa6-2b96c79aa276

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 338, k = 56953 := by
  rw [sum_range_id]
