-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.annih_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T12:39:58.273195+00:00
-- url     : https://prove2.me/submissions/b89e9cb3-6840-4e2a-9d5d-32c7a9658090

import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock

variable {M : Type*} [DecidableEq M]

theorem solution (m : M) : annih m (vacuum : FockDom M) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  change annihCoeff m ((lp.single 2 (0 : Conf M) 1 : Conf M → ℂ)) n = 0
  unfold annihCoeff
  have hne : n + Finsupp.single m 1 ≠ (0 : Conf M) := by
    intro h
    have hm := congrArg (fun f : Conf M => f m) h
    simp at hm
  simp [lp.single_apply, hne]
