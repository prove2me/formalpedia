-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgGhostCar_book
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:24:32.860988+00:00
-- url     : https://prove2.me/submissions/4713511f-2436-4427-8c6b-104a9e6dacd4

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
import Theorems.Thm_BookProof_QuantumGravityFock_qgGhostCar
import Theorems.Thm_BookProof_QuantumGravityFock_qgGhostCar_of_ne
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGhostCar_book
open BookProof.FockSecondQuantization
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (a b : Fin qgGhostModes) (z : QGGraded) :
    ghostOp (fermAnn a.val) (ghostOp (fermCre b.val) z)
        + ghostOp (fermCre b.val) (ghostOp (fermAnn a.val) z)
      = if a = b then z else 0 := by
  split_ifs with h
  · subst h
    exact BookProof.QuantumGravityFock.qgGhostCar a.val z
  · exact BookProof.QuantumGravityFock.qgGhostCar_of_ne (fun e => h (Fin.ext e)) z

