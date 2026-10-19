-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgTwoLevel_esa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:39:40.57877+00:00
-- url     : https://prove2.me/submissions/5cf1a379-f01b-4160-89c9-ff9198736d69

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
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
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hTwoLevel_hasZeroDeficiencyOn
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgTwoLevel_esa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (ext eps : ℕ → ℝ) :
    HasZeroDeficiencyOn (BookProof.NavierStokesFlow.FockOfFock.FockOfFockDom ℕ ℕ)
      (BookProof.NavierStokesFlow.FockOfFock.hTwoLevel ext eps) := by
  exact BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn ext eps

