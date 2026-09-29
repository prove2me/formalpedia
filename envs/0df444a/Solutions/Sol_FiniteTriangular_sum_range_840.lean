-- Prove2me | solution 1 for FiniteTriangular.sum_range_840
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:23.867723+00:00
-- url     : https://prove2.me/submissions/d893fba6-6c18-4ea4-8786-3362edfbc283

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 840, k = 352380 := by
  rw [sum_range_id]
