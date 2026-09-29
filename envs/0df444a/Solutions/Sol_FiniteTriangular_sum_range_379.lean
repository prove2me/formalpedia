-- Prove2me | solution 1 for FiniteTriangular.sum_range_379
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:21.255652+00:00
-- url     : https://prove2.me/submissions/252a527d-78bb-4154-ae43-a110e25af6ba

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 379, k = 71631 := by
  rw [sum_range_id]
