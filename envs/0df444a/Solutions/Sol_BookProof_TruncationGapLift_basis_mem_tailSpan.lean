-- Prove2me | solution 1 for BookProof.TruncationGapLift.basis_mem_tailSpan
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:14.89487+00:00
-- url     : https://prove2.me/submissions/1920f7ce-74a2-44e0-ba10-5d263ec8336f

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.basis_mem_tailSpan
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
open BookProof.TruncationGapLift



noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : m ≤ i) :
    b i ∈ tailSpan b m := Submodule.subset_span ⟨i, him, rfl⟩
