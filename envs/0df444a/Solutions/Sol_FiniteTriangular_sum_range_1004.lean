-- Prove2me | solution 1 for FiniteTriangular.sum_range_1004
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:50.587984+00:00
-- url     : https://prove2.me/submissions/448e1277-db08-4101-91e8-5396faf6c070

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1004, k = 503506 := by
  rw [sum_range_id]
