-- Prove2me | solution 1 for BookProof.FockStatistics.cfermionicProj_sectorEmb_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T08:45:16.926204+00:00
-- url     : https://prove2.me/submissions/707bc51a-a949-48c8-b900-9c9eadda35aa

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.cfermionicProj_sectorEmb_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_apply
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterTensorPermutation
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector
open BookProof.SecondQuantizationCore
open BookProof.TensorPerm

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x : (Hs.pow n).carrier) :
    cfermionicProj Hs n (sectorEmb Hs n x) = sectorEmb Hs n (fermionicProj Hs n x) := by

  rw [cfermionicProj, UnitaryRep.avgProj_apply, fermionicProj, UnitaryRep.avgProj_apply,
    map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => (signRep Hs n).completionRep_act_coe g x)
