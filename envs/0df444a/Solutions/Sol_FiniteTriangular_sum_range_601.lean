-- Prove2me | solution 1 for FiniteTriangular.sum_range_601
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:53.249689+00:00
-- url     : https://prove2.me/submissions/075f9574-1db6-4312-9a8e-511fc6682695

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 601, k = 180300 := by
  rw [sum_range_id]
