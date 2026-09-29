-- Prove2me | solution 1 for FiniteTriangular.sum_range_636
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:51.101605+00:00
-- url     : https://prove2.me/submissions/7f6eeedd-48ea-45cf-beee-1f134f45dd53

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 636, k = 201930 := by
  rw [sum_range_id]
