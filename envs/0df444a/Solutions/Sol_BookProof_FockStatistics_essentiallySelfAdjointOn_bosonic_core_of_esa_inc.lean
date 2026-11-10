-- Prove2me | solution 1 for BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_core_of_esa_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T03:42:22.972738+00:00
-- url     : https://prove2.me/submissions/2d699b06-baa4-43d7-8a9b-d2d8b50e6c39

-- Generated from ChapterFockStatisticsEsa.lean — solution of BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_core_of_esa_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsEsa
import Theorems.Thm_BookProof_FockStatistics_essentiallySelfAdjointOn_sectorDom_of_esa
import Theorems.Thm_BookProof_PermSector_essentiallySelfAdjointOn_bosonic_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterScalarDGammaEsa
open BookProof.DirectSumEsa
open BookProof.GraphCore
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
variable {D₀ : Submodule ℂ Hs.carrier}

set_option maxHeartbeats 1000000 in
include hdense hesa hsym in
theorem solution (hcore : IsGraphCore D₀ A) (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (bosonicProj Hs n) (sectorCore Hs D D₀ n))
      (bosonicCoreOp Hs D A D₀ n) := 
  essentiallySelfAdjointOn_bosonic_core (Hs := Hs) (D₂ := D) (A := A) (D := D₀)
      n hcore
      (essentiallySelfAdjointOn_sectorDom_of_esa (Hs := Hs) (D := D) A hdense hsym hesa n)
