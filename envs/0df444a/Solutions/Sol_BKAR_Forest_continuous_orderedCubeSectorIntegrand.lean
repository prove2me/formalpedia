-- Prove2me | solution 1 for BKAR.Forest.continuous_orderedCubeSectorIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:34.670858+00:00
-- url     : https://prove2.me/submissions/75269f56-d954-4cd9-8e60-d351f8028bae

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
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
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Continuous
      (fun u : F.EdgeParam → ℝ =>
        mixedPartialList order.reverse ρ (F.standardInterp u)) := by
  exact (hρ.mixedPartialList_continuous order.reverse).comp
    (F.standardInterp_continuous_comp continuous_id)
end BKAR.Forest
