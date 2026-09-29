-- Prove2me | solution 1 for FiniteTriangular.sum_range_633
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:49.343996+00:00
-- url     : https://prove2.me/submissions/1a2dcaa2-a877-4d18-9390-af7247bbc309

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 633, k = 200028 := by
  rw [sum_range_id]
