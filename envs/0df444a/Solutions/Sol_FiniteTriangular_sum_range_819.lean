-- Prove2me | solution 1 for FiniteTriangular.sum_range_819
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:54.723912+00:00
-- url     : https://prove2.me/submissions/ecdb66cd-d2b4-4637-b139-91545f2e130f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 819, k = 334971 := by
  rw [sum_range_id]
