-- Prove2me | solution 1 for FiniteTriangular.sum_range_610
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:42.181782+00:00
-- url     : https://prove2.me/submissions/5642c41e-8461-4ccc-9482-6d410d0c9e94

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 610, k = 185745 := by
  rw [sum_range_id]
