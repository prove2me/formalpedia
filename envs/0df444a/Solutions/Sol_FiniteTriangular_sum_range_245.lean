-- Prove2me | solution 1 for FiniteTriangular.sum_range_245
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:25.845506+00:00
-- url     : https://prove2.me/submissions/d342b163-ca60-436d-a2fa-88eab593ac33

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 245, k = 29890 := by
  rw [sum_range_id]
