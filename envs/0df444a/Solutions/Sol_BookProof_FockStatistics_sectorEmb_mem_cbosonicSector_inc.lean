-- Prove2me | solution 1 for BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T09:51:16.964343+00:00
-- url     : https://prove2.me/submissions/c6e800e2-254d-435c-a713-35f22390fa42

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_cbosonicProj_sectorEmb_inc
import Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj
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
    (hx : x ∈ sector (bosonicProj Hs n)) : sectorEmb Hs n x ∈ sector (cbosonicProj Hs n) :=
  ⟨sectorEmb Hs n x, by
      rw [cbosonicProj_sectorEmb]
      exact congrArg (sectorEmb Hs n) ((isReducingProjection_bosonicProj Hs n).apply_of_mem_range hx)⟩
