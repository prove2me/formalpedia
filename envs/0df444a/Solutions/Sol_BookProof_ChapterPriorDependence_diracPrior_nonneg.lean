-- Prove2me | solution 1 for BookProof.ChapterPriorDependence.diracPrior_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:36.025022+00:00
-- url     : https://prove2.me/submissions/07c9618a-9372-46d5-9c5e-1235461de268

-- Generated from ChapterPriorDependence.lean — solution of BookProof.ChapterPriorDependence.diracPrior_nonneg
import Mathlib
import Definitions.Def_ChapterPriorDependence
open BookProof.ChapterPriorDependence



open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable {Hyp Data : Type*} [DecidableEq Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (a x : Hyp) : 0 ≤ diracPrior a x := by

  unfold diracPrior
  split_ifs <;> norm_num
