-- Prove2me | solution 1 for FiniteTriangular.sum_range_982
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:13.097524+00:00
-- url     : https://prove2.me/submissions/46ba8ad3-f242-4787-a79a-ef34b2ae82ba

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 982, k = 481671 := by
  rw [sum_range_id]
