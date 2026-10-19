-- Prove2me | solution 1 for BookProof.QuantumGravityFock.bosOp_even
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:24:14.108995+00:00
-- url     : https://prove2.me/submissions/cdd94824-fd4c-45c1-901f-23fef09633e3

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
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.bosOp_even
open BookProof.FockSecondQuantization
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (A : BoseAlg →ₗ[ℂ] BoseAlg) (z : QGGraded) :
    qgGrade (bosOp A z) = bosOp A (qgGrade z) := by
  have h : qgGrade.comp (bosOp A) = (bosOp A).comp qgGrade := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact LinearMap.congr_fun h z

