-- Prove2me | solution 1 for BookProof.FockStatistics.sectorEmb_mem_cfermionicSector_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T09:53:42.63723+00:00
-- url     : https://prove2.me/submissions/b3b10a5c-3ca6-47d0-994a-1c2ab82b56bd

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.sectorEmb_mem_cfermionicSector_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_cfermionicProj_sectorEmb_inc
import Theorems.Thm_BookProof_PermSector_isReducingProjection_fermionicProj
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.TensorCore
open BookProof.FarisLavine
open BookProof.PermSector
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) {x : (Hs.pow n).carrier}
    (hx : x ∈ sector (fermionicProj Hs n)) :
    sectorEmb Hs n x ∈ sector (cfermionicProj Hs n) :=
  ⟨sectorEmb Hs n x, by
      rw [cfermionicProj_sectorEmb]
      exact congrArg (sectorEmb Hs n)
        ((isReducingProjection_fermionicProj Hs n).apply_of_mem_range hx)⟩
