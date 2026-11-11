-- Prove2me | solution 1 for BookProof.FockStatistics.hfermionicFock_symmetricOn_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T09:49:53.511213+00:00
-- url     : https://prove2.me/submissions/af4518db-004d-430b-a92f-94b3915adf9f

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.hfermionicFock_symmetricOn_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_symmetricOn_cfermionic_inc
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
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
include hsym in
theorem solution :
    SymmetricOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A) := dsOp_symmetricOn _ (fun n => symmetricOn_cfermionic A hsym n)
