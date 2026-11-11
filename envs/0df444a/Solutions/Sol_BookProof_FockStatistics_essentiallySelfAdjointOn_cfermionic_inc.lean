-- Prove2me | solution 1 for BookProof.FockStatistics.essentiallySelfAdjointOn_cfermionic_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T08:47:57.010044+00:00
-- url     : https://prove2.me/submissions/aa6d1526-09c3-4f7c-bc07-f4c74a01dde8

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.essentiallySelfAdjointOn_cfermionic_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterA
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.TensorCore
open BookProof.FarisLavine
open BookProof.SecondQuantizationCore
open BookProof.EsaOneParticle

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
include hdense hesa hsym in
theorem solution (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (cfermionicProj Hs n) (fockSectorDom Hs D n))
      (cfermionicSectorOp Hs D A n) :=
  essentiallySelfAdjointOn_red _ _
      (essentiallySelfAdjointOn_fockSectorDom_esa A hdense hsym hesa n)
