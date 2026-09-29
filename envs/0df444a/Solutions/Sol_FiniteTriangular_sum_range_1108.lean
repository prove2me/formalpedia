-- Prove2me | solution 1 for FiniteTriangular.sum_range_1108
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:32.496594+00:00
-- url     : https://prove2.me/submissions/f181b744-29ff-4e35-af49-fac934e96745

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1108, k = 613278 := by
  rw [sum_range_id]
