-- Prove2me | solution 1 for BookProof.QedFockGapChain.photonDispersion_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:48:05.713572+00:00
-- url     : https://prove2.me/submissions/96f4770f-4f41-4498-add5-de9e1b58f3ae

-- Generated from ChapterQedFockGapChain.lean — solution of BookProof.QedFockGapChain.photonDispersion_nonneg
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.QedFockGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.FockDiagonalGapChain BookProof.YangMillsFriedrichs
open MeasureTheory


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) (k : ℕ) : 0 ≤ photonDispersion p k := abs_nonneg _
