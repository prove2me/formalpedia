-- Prove2me | solution 1 for FiniteTriangular.sum_range_759
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:14.897188+00:00
-- url     : https://prove2.me/submissions/c00777ac-c621-4aa2-8fcf-3424199042b3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 759, k = 287661 := by
  rw [sum_range_id]
