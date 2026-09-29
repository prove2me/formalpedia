-- Prove2me | solution 1 for FiniteTriangular.sum_range_794
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:43.756607+00:00
-- url     : https://prove2.me/submissions/8fac700d-7c2d-469d-9045-f16097da29fb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 794, k = 314821 := by
  rw [sum_range_id]
