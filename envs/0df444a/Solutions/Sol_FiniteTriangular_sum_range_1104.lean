-- Prove2me | solution 1 for FiniteTriangular.sum_range_1104
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:44.857558+00:00
-- url     : https://prove2.me/submissions/6fe1186b-c467-4c8f-8fbc-7c1f4c8fbd1c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1104, k = 608856 := by
  rw [sum_range_id]
