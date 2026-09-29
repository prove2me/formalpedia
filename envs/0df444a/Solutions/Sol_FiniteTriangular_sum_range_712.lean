-- Prove2me | solution 1 for FiniteTriangular.sum_range_712
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:07:00.820409+00:00
-- url     : https://prove2.me/submissions/05675d8a-8d10-484f-b752-59e8910ed5ae

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 712, k = 253116 := by
  rw [sum_range_id]
