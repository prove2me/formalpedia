-- Prove2me | solution 1 for BookProof.FockStatistics.mem_cbosonicSector_iff_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T08:06:29.167891+00:00
-- url     : https://prove2.me/submissions/90cfb71f-4fe8-4991-a25e-82a166c58776

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.mem_cbosonicSector_iff_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_mem_range_avgProj_iff
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) {x : fockSector Hs n} :
    x ∈ sector (cbosonicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (cpermRep Hs n).act σ x = x := (cpermRep Hs n).mem_range_avgProj_iff
