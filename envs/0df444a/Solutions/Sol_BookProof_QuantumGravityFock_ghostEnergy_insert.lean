-- Prove2me | solution 1 for BookProof.QuantumGravityFock.ghostEnergy_insert
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:36:55.013541+00:00
-- url     : https://prove2.me/submissions/33f453ea-a482-48b6-a723-2c10448b6f4d

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
import Definitions.Def_ChapterYangMillsGhostSector
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.ghostEnergy_insert
open BookProof.YangMillsGhost
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution {g : ℕ → ℝ} {a : ℕ} {α : FermConf} (h : a ∉ α) :
    ghostEnergy g (insert a α) = g a + ghostEnergy g α := by
  simp only [BookProof.QuantumGravityFock.ghostEnergy]
  exact Finset.sum_insert h

