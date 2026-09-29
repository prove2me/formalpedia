-- Prove2me | solution 1 for FiniteTriangular.sum_range_767
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:52.566107+00:00
-- url     : https://prove2.me/submissions/13623dad-967a-46c5-bd1f-268c1dc53400

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 767, k = 293761 := by
  rw [sum_range_id]
