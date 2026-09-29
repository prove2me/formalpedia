-- Prove2me | solution 1 for FiniteTriangular.sum_range_900
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:44.681909+00:00
-- url     : https://prove2.me/submissions/8b8dc82e-77ba-482e-9719-3165b52dab92

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 900, k = 404550 := by
  rw [sum_range_id]
