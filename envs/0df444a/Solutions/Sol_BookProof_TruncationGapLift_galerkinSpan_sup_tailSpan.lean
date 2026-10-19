-- Prove2me | solution 1 for BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:10:47.05672+00:00
-- url     : https://prove2.me/submissions/fe44a5b5-9564-4004-a209-13a4334ca2c5

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.TruncationGapLift



noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ⊔ tailSpan b m = finiteModeDomain b := by

  have hset : ({i | i < m} ∪ {i | m ≤ i} : Set ℕ) = Set.univ := by
    ext i
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    omega
  rw [galerkinSpan, tailSpan, ← Submodule.span_union, ← Set.image_union, hset,
    Set.image_univ, finiteModeDomain]
