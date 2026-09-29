-- Prove2me | solution 2 for BookProof.NavierStokesFlow.FockOfFock.outerOneParticle
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:32.792646+00:00
-- url     : https://prove2.me/submissions/8b0164ab-86a3-4499-9b03-8b66f1d179fa

-- Generated from ChapterNavierStokesFockSpace.lean — solution of BookProof.NavierStokesFlow.FockOfFock.outerOneParticle
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_vacuum
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock









open BookProof.NavierStokesFlow.FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

































variable {J K : Type*} [DecidableEq J] [DecidableEq K]

set_option maxHeartbeats 1000000 in
theorem solution (j : J) (c : Conf K) :
    creat (j, c) (vacuum : FockOfFockDom J K) = fockBasis (Finsupp.single (j, c) 1) := creat_vacuum _
