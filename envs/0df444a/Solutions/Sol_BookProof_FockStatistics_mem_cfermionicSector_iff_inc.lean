-- Prove2me | solution 1 for BookProof.FockStatistics.mem_cfermionicSector_iff_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T08:48:46.625681+00:00
-- url     : https://prove2.me/submissions/c507d54d-3c1f-4416-b2b1-8c3364ec5922

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.mem_cfermionicSector_iff_inc
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
    x ∈ sector (cfermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (csignRep Hs n).act σ x = x := (csignRep Hs n).mem_range_avgProj_iff
