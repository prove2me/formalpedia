-- Prove2me | solution 1 for BookProof.QuantumGravityFock.bosOp_ghostOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:23:50.625509+00:00
-- url     : https://prove2.me/submissions/37ed48fa-ecf6-41f2-ae80-7035074030f3

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterFockSecondQuantization
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.bosOp_ghostOp_comm
open BookProof.FockSecondQuantization
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (A : BoseAlg →ₗ[ℂ] BoseAlg) (B : FermAlg →ₗ[ℂ] FermAlg)
    (z : QGGraded) : bosOp A (ghostOp B z) = ghostOp B (bosOp A z) := by
  have h : (bosOp A).comp (ghostOp B) = (ghostOp B).comp (bosOp A) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact LinearMap.congr_fun h z

