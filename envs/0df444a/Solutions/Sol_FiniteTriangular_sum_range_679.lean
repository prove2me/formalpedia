-- Prove2me | solution 1 for FiniteTriangular.sum_range_679
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:14.94206+00:00
-- url     : https://prove2.me/submissions/802d431f-e1ad-47c1-a157-87a58cd6182c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 679, k = 230181 := by
  rw [sum_range_id]
