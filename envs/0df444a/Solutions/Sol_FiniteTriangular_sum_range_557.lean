-- Prove2me | solution 1 for FiniteTriangular.sum_range_557
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:26.948747+00:00
-- url     : https://prove2.me/submissions/174be015-ffab-41ec-bf22-b4ed96a7870b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 557, k = 154846 := by
  rw [sum_range_id]
