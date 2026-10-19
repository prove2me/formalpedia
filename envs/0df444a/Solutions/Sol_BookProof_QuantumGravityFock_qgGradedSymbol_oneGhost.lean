-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:37:05.020931+00:00
-- url     : https://prove2.me/submissions/62eb1dc9-eaaf-488d-9838-63df0654f7a4

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
import Definitions.Def_ChapterFockSecondQuantization
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterYangMillsGhostSector
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost
open BookProof.FockOneParticleGap
open BookProof.YangMillsGhost
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (omega g : ℕ → ℝ) (a : ℕ) :
    qgGradedSymbol omega g (0, ({a} : FermConf)) = g a := by
  simp [qgGradedSymbol, BookProof.QuantumGravityFock.ghostEnergy, BookProof.NavierStokesFlow.FockOfFock.confEnergy_zero]

