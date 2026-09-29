-- Prove2me | solution 1 for FiniteTriangular.sum_range_451
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:00.846166+00:00
-- url     : https://prove2.me/submissions/e1bf5504-3619-41ee-850e-3e53009b69fd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 451, k = 101475 := by
  rw [sum_range_id]
