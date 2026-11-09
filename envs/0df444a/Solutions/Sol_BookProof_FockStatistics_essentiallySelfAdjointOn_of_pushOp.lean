-- Prove2me | solution 1 for BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T20:42:34.462308+00:00
-- url     : https://prove2.me/submissions/4eecc632-21c2-4110-a5bb-496e38fc0285

-- Generated from ChapterFockStatisticsEsa.lean — solution of BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Theorems.Thm_BookProof_FockStatistics_deficiencyTrivialAt_of_pushOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFockStatisticsCompletion
open BookProof.FockStatistics




open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.EsaOneParticle BookProof.DirectSumEsa
open BookProof.GraphCore

noncomputable section

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    (T : D →ₗ[ℂ] F) (h : EssentiallySelfAdjointOn (pushDom U D) (pushOp U T)) :
    EssentiallySelfAdjointOn D T := ⟨deficiencyTrivialAt_of_pushOp U T h.1, deficiencyTrivialAt_of_pushOp U T h.2⟩
