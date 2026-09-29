-- Prove2me | solution 1 for FiniteTriangular.sum_range_843
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:56.594241+00:00
-- url     : https://prove2.me/submissions/abba08ce-91f1-4338-bc46-bb4a2908556c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 843, k = 354903 := by
  rw [sum_range_id]
