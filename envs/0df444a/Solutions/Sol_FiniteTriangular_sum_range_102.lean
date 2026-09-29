-- Prove2me | solution 1 for FiniteTriangular.sum_range_102
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:38.242979+00:00
-- url     : https://prove2.me/submissions/eba35e5f-d46e-45ca-a04d-dbfed5693790

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 102, k = 5151 := by
  decide
