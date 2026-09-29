-- Prove2me | solution 1 for FiniteTriangular.sum_range_970
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:24.340203+00:00
-- url     : https://prove2.me/submissions/253ec2f3-2bfe-4605-9a8c-d4a2d45b3b76

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 970, k = 469965 := by
  rw [sum_range_id]
