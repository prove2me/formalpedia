-- Prove2me | solution 1 for BookProof.FockStatistics.symmetricOn_cbosonic_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T08:09:06.231659+00:00
-- url     : https://prove2.me/submissions/51e59ffb-2d6c-431c-85ea-8c1aaa301f7c

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.symmetricOn_cbosonic_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_GraphCore_symmetricOn_pushOp
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
import Theorems.Thm_BookProof_ReducedEsa_symmetricOn_redOp
import Theorems.Thm_BookProof_TensorCore_symmetricOn_sectorOp
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterA
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.TensorCore
open BookProof.FarisLavine
open BookProof.GraphCore
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
include hsym in
theorem solution (n : ℕ) :
    SymmetricOn (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n))
      (cbosonicSectorOp Hs D A n) :=
  symmetricOn_redOp _ _
      (symmetricOn_pushOp (sectorEmb Hs n) (sectorOp Hs D A n)
        (symmetricOn_sectorOp Hs D A hsym n))
