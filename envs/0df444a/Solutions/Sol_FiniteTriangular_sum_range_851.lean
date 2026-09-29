-- Prove2me | solution 1 for FiniteTriangular.sum_range_851
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:32.32992+00:00
-- url     : https://prove2.me/submissions/eec09862-b234-4589-be45-2f3532ddb92d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 851, k = 361675 := by
  rw [sum_range_id]
