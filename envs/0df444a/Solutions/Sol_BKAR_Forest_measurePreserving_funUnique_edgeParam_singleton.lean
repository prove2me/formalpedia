-- Prove2me | solution 1 for BKAR.Forest.measurePreserving_funUnique_edgeParam_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:19.56472+00:00
-- url     : https://prove2.me/submissions/d2ace0cf-a28e-45ef-92d6-4bf2851bc8d5

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    MeasurePreserving
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance)
      (volume : Measure (F.EdgeParam → ℝ)) (volume : Measure ℝ) := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  rw [volume_pi]
  convert measurePreserving_funUnique (volume : Measure ℝ) F.EdgeParam using 2; rfl
end BKAR.Forest
