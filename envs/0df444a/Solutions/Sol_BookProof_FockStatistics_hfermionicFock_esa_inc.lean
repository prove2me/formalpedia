-- Prove2me | solution 1 for BookProof.FockStatistics.hfermionicFock_esa_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T09:49:40.615823+00:00
-- url     : https://prove2.me/submissions/8513f4d9-b357-49b7-8086-d446a3f2deea

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.hfermionicFock_esa_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_essentiallySelfAdjointOn_cfermionic_inc
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterDirectSumEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.TensorCore
open BookProof.FarisLavine
open BookProof.DirectSumEsa

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
include hdense hesa hsym in
theorem solution :
    EssentiallySelfAdjointOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A) :=
  dsOp_essentiallySelfAdjointOn _
      (fun n => essentiallySelfAdjointOn_cfermionic A hdense hsym hesa n)
