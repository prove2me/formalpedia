-- Prove2me | solution 1 for FiniteTriangular.sum_range_1114
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:06.11263+00:00
-- url     : https://prove2.me/submissions/435ce2d1-7607-4401-ae8d-46edc41f06e5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1114, k = 619941 := by
  rw [sum_range_id]
