-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.creat_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:31.391662+00:00
-- url     : https://prove2.me/submissions/a0fd9256-41ff-48cc-958a-c0b5572004c0

-- Generated from ChapterNavierStokesFockSpace.lean — solution of BookProof.NavierStokesFlow.FockOfFock.creat_vacuum
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_basis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock









open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution (m : M) :
    creat m (vacuum : FockDom M) = fockBasis (Finsupp.single m 1) := by

  rw [vacuum, creat_basis]
  simp
