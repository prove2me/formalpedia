-- Prove2me | solution 1 for FiniteTriangular.sum_range_871
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:42:00.756148+00:00
-- url     : https://prove2.me/submissions/db1fead6-ecc1-4b40-b6b2-ca0336fc69b6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 871, k = 378885 := by
  rw [sum_range_id]
