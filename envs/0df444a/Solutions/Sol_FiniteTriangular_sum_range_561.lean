-- Prove2me | solution 1 for FiniteTriangular.sum_range_561
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:16.648673+00:00
-- url     : https://prove2.me/submissions/d4f45524-3bf0-4fdb-8688-5dbae3e24afd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 561, k = 157080 := by
  rw [sum_range_id]
