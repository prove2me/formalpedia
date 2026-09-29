-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.add_single_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:13:16.496026+00:00
-- url     : https://prove2.me/submissions/ea858472-c14d-4de8-96df-e8bc347af7de

import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock
open FullEsa
variable {ι : Type*}
variable {M : Type*} [DecidableEq M]

theorem solution (m : M) (n : Conf M) :
    (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n := by
  ext j
  by_cases h : j = m <;> simp [h]
