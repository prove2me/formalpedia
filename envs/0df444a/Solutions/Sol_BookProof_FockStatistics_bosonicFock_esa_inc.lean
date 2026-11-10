-- Prove2me | solution 1 for BookProof.FockStatistics.bosonicFock_esa_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T03:42:19.19122+00:00
-- url     : https://prove2.me/submissions/0928bca4-8925-4005-b4c5-763712fc685d

-- Generated from ChapterFockStatisticsEsa.lean — solution of BookProof.FockStatistics.bosonicFock_esa_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Theorems.Thm_BookProof_PermSector_essentiallySelfAdjointOn_bosonic
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterScalarDGammaEsa
import Theorems.Thm_BookProof_FockStatistics_essentiallySelfAdjointOn_sectorDom_of_esa
open BookProof.TensorCore



open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.DirectSumEsa
open BookProof.FockStatistics
open BookProof.GroupAverage BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.EsaOneParticle BookProof.DirectSumEsa

noncomputable section

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
include hdense hesa hsym in
theorem solution :
    EssentiallySelfAdjointOn (bosonicFockDom Hs D) (bosonicFockOp Hs D A) := 
  dsOp_essentiallySelfAdjointOn (fun n : ℕ => bosonicSectorOp Hs D A n)
      (fun n => essentiallySelfAdjointOn_bosonic Hs D A n
        (essentiallySelfAdjointOn_sectorDom_of_esa A hdense hsym hesa n))
