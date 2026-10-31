-- Prove2me | solution 1 for BookProof.QedFockGapChain.irPhotonDispersion_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:48:24.339004+00:00
-- url     : https://prove2.me/submissions/f0c1b375-e095-4e45-a1a8-9628328a5809

-- Generated from ChapterQedFockGapChain.lean — solution of BookProof.QedFockGapChain.irPhotonDispersion_ge
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
theorem solution (mu : ℝ) (p : ℕ → ℝ) (k : ℕ) :
    mu ≤ irPhotonDispersion mu p k := le_max_left _ _
