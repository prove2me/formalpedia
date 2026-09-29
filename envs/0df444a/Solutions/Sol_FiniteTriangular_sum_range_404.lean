-- Prove2me | solution 1 for FiniteTriangular.sum_range_404
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:32.711885+00:00
-- url     : https://prove2.me/submissions/e5b532a3-5702-4476-bdd0-21464ba8edf4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 404, k = 81406 := by
  rw [sum_range_id]
