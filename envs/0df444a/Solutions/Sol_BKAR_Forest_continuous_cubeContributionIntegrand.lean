-- Prove2me | solution 1 for BKAR.Forest.continuous_cubeContributionIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:34.131402+00:00
-- url     : https://prove2.me/submissions/a1bdea48-55ff-4b0b-9648-71414e4c09cb

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous
import Theorems.Thm_BKAR_Forest_mixedPartial_def
import Theorems.Thm_BKAR_Forest_standardInterp_continuous_comp
import Theorems.Thm_BKAR_ListPathContinuous_comp


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    Continuous
      (fun u : F.EdgeParam → ℝ =>
        F.mixedPartial ρ (F.standardInterp u)) := by
  have hinterp :
      Continuous (fun u : F.EdgeParam → ℝ => F.standardInterp u) :=
    F.standardInterp_continuous_comp continuous_id
  have hpartial : Continuous (F.mixedPartial ρ) := by
    rw [mixedPartial_def]
    exact hρ.mixedPartialList_continuous F.edges.toList
  exact hpartial.comp hinterp
end BKAR.Forest
