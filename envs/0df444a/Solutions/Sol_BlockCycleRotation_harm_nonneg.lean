-- Prove2me | solution 1 for BlockCycleRotation.harm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T10:53:10.164974+00:00
-- url     : https://prove2.me/submissions/cfe25739-c23c-47d2-aa12-73cb82685d89

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem solution (a : ℕ) : 0 ≤ harm a := by
  unfold harm
  exact Finset.sum_nonneg fun i _ => by positivity
