-- Prove2me | solution 1 for FiniteTriangular.sum_range_443
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:14.318493+00:00
-- url     : https://prove2.me/submissions/a07a9768-df0f-49a9-8dd0-466dcadff3e8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 443, k = 97903 := by
  rw [sum_range_id]
