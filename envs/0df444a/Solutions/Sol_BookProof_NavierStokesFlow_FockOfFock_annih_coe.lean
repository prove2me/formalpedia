-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.annih_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:47:54.104554+00:00
-- url     : https://prove2.me/submissions/325e3683-d8e0-4259-96dc-a23ce389ab23

import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock
open FullEsa

variable {M : Type*} [DecidableEq M]

theorem solution (m : M) (f : FockDom M) (n : Conf M) :
    (((annih m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m + 1) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n + Finsupp.single m 1) := by
  rfl
