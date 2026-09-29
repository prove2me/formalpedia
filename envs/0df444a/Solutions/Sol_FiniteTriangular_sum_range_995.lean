-- Prove2me | solution 1 for FiniteTriangular.sum_range_995
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:48.392251+00:00
-- url     : https://prove2.me/submissions/4d063cc8-91d1-4b69-9ca8-fd54180ffa2b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 995, k = 494515 := by
  rw [sum_range_id]
