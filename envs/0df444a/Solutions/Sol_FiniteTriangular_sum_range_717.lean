-- Prove2me | solution 1 for FiniteTriangular.sum_range_717
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:53.378812+00:00
-- url     : https://prove2.me/submissions/f5d4a695-7471-401b-81eb-cb3ef0c3a9de

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 717, k = 256686 := by
  rw [sum_range_id]
