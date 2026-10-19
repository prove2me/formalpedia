-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:41:05.273098+00:00
-- url     : https://prove2.me/submissions/d093d9cb-17c7-4582-8c26-630435bfdce4

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
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_hasZeroDeficiencyOn
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (omega g : ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes GradedIdx)
      ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) := by
  obtain ⟨h1, h2⟩ := BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn (qgGradedSymbol omega g)
  constructor
  · intro w hw
    apply h1 w
    intro v
    rw [inner_smul_right]
    exact hw v
  · intro w hw
    apply h2 w
    intro v
    rw [inner_neg_right, inner_smul_right, ← neg_mul]
    exact hw v

