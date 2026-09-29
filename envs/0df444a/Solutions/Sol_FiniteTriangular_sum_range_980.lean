-- Prove2me | solution 1 for FiniteTriangular.sum_range_980
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:11.909238+00:00
-- url     : https://prove2.me/submissions/dd6edd33-ca2b-467d-bd1d-b41d41cdb7bc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 980, k = 479710 := by
  rw [sum_range_id]
