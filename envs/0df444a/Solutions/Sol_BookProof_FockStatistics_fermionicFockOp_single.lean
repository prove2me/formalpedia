-- Prove2me | solution 1 for BookProof.FockStatistics.fermionicFockOp_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T14:43:07.323556+00:00
-- url     : https://prove2.me/submissions/9277882c-0b1b-4ee7-863c-99bfddc63129

-- Generated from ChapterFockStatisticsEsa.lean — solution of BookProof.FockStatistics.fermionicFockOp_single
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_single
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
open BookProof.FockStatistics




open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.EsaOneParticle BookProof.DirectSumEsa
open BookProof.TensorCore

noncomputable section

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)
variable (D₀ : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ)
    (u : redDom (fermionicProj Hs n) (sectorDom Hs D n)) :
    (fermionicFockOp Hs D A ⟨lp.single 2 n ((u : sector (fermionicProj Hs n))),
        single_mem_dsCore (D := fun n : ℕ => redDom (fermionicProj Hs n) (sectorDom Hs D n))
          n u⟩ : fermionicFock Hs)
      = lp.single 2 n (fermionicSectorOp Hs D A n u) := dsOp_single (fun n : ℕ => fermionicSectorOp Hs D A n) n u
