-- Prove2me | solution 1 for FiniteTriangular.sum_range_808
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:31.296602+00:00
-- url     : https://prove2.me/submissions/11c3bb35-cdf2-4637-afd7-bceb79eefd15

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 808, k = 326028 := by
  rw [sum_range_id]
