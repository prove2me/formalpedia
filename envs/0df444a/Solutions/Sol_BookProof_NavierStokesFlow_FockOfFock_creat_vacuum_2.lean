-- Prove2me | solution 2 for BookProof.NavierStokesFlow.FockOfFock.creat_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:31.759907+00:00
-- url     : https://prove2.me/submissions/5a742d67-c2ab-428d-9045-4d60106dc10c

-- Generated from ChapterNavierStokesFockSpace.lean — solution of BookProof.NavierStokesFlow.FockOfFock.creat_vacuum
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_basis
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock









open BookProof.NavierStokesFlow.FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution (m : M) :
    creat m (vacuum : FockDom M) = fockBasis (Finsupp.single m 1) := by

  rw [vacuum, creat_basis]
  simp
