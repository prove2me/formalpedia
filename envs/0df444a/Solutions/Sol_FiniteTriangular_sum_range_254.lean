-- Prove2me | solution 1 for FiniteTriangular.sum_range_254
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:17.514131+00:00
-- url     : https://prove2.me/submissions/d5e96771-c893-4487-85ad-7d7b2801bf0e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 254, k = 32131 := by
  rw [sum_range_id]
