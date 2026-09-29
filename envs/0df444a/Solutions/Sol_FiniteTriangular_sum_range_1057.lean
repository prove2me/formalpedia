-- Prove2me | solution 1 for FiniteTriangular.sum_range_1057
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:00.103175+00:00
-- url     : https://prove2.me/submissions/540d06cd-2b14-40fa-86d8-b341dcc2ee37

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1057, k = 558096 := by
  rw [sum_range_id]
