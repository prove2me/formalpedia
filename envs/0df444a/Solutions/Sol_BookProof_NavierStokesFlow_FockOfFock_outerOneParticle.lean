-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.outerOneParticle
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:09.74212+00:00
-- url     : https://prove2.me/submissions/bb580eab-6c4e-4e10-82eb-2f6ba12b3fed

-- Generated from ChapterNavierStokesFockSpace.lean — solution of BookProof.NavierStokesFlow.FockOfFock.outerOneParticle
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_vacuum
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock









open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

































variable {J K : Type*} [DecidableEq J] [DecidableEq K]

set_option maxHeartbeats 1000000 in
theorem solution (j : J) (c : Conf K) :
    creat (j, c) (vacuum : FockOfFockDom J K) = fockBasis (Finsupp.single (j, c) 1) := creat_vacuum _
