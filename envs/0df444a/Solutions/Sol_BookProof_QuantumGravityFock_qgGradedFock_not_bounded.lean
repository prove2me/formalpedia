-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgGradedFock_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:41:28.751414+00:00
-- url     : https://prove2.me/submissions/0c920f65-32e0-4da2-8be3-d68f3a4dfe83

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
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_not_bounded
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_not_bounded
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.YangMillsGhost
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (omega g : ℕ → ℝ) (homega : omega = 0)
    (hg : ∀ C : ℝ, ∃ a, C < |g a|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes GradedIdx, ‖qgGradedHam omega g f‖ ≤ C * ‖f‖ := by
  apply BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded
  intro C
  obtain ⟨a, ha⟩ := hg C
  refine ⟨(0, {a}), ?_⟩
  simpa [qgGradedSymbol, BookProof.QuantumGravityFock.ghostEnergy, BookProof.NavierStokesFlow.FockOfFock.confEnergy_zero] using ha

