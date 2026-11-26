-- Prove2me | solution 1 for BKAR.Forest.integrableOn_orderedCubeSectorIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:43.468667+00:00
-- url     : https://prove2.me/submissions/deb7d22a-8dfa-4ae2-9614-2b8ed8ef9625

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_Forest_continuous_orderedCubeSectorIntegrand
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_isCompact_unitCube


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
    IntegrableOn
      (fun u : F.EdgeParam → ℝ =>
        mixedPartialList order.reverse ρ (F.standardInterp u))
      F.unitCube (volume : Measure (F.EdgeParam → ℝ)) :=
  (F.continuous_orderedCubeSectorIntegrand order ρ hρ).continuousOn.integrableOn_compact
    F.isCompact_unitCube
end BKAR.Forest
