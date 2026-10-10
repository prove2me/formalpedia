-- Prove2me | solution 1 for BookProof.ChapterPriorDependence.diracPrior_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:37.112072+00:00
-- url     : https://prove2.me/submissions/afd51af8-bba8-472b-826b-4ab5008f4d05

-- Generated from ChapterPriorDependence.lean — solution of BookProof.ChapterPriorDependence.diracPrior_sum_one
import Mathlib
import Definitions.Def_ChapterPriorDependence
open BookProof.ChapterPriorDependence



open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable {Hyp Data : Type*} [DecidableEq Hyp]
variable [Fintype Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (a : Hyp) : ∑ x, diracPrior a x = 1 := by

  unfold diracPrior
  aesop
