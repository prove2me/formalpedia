-- Prove2me | solution 1 for BKAR.Forest.integrableOn_cubeContributionIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:43.983521+00:00
-- url     : https://prove2.me/submissions/97770597-f2b5-4dcf-9e16-37257a537695

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_Forest_continuous_cubeContributionIntegrand
import Theorems.Thm_BKAR_Forest_isCompact_unitCube


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
    IntegrableOn
      (fun u : F.EdgeParam → ℝ =>
        F.mixedPartial ρ (F.standardInterp u))
      F.unitCube (volume : Measure (F.EdgeParam → ℝ)) :=
  (F.continuous_cubeContributionIntegrand ρ hρ).continuousOn.integrableOn_compact
    F.isCompact_unitCube
end BKAR.Forest
