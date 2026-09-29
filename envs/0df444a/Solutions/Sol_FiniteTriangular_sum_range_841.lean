-- Prove2me | solution 1 for FiniteTriangular.sum_range_841
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:55.345794+00:00
-- url     : https://prove2.me/submissions/f5e25a42-fc07-47a5-9f7d-f4706e709728

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 841, k = 353220 := by
  rw [sum_range_id]
