-- Prove2me | solution 1 for BKAR.Forest.measurableSet_orderedCubeSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:43.462497+00:00
-- url     : https://prove2.me/submissions/d8381ebf-7c7c-42f1-bc56-6000d645132e

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_measurableSet_unitCube
import Theorems.Thm_BKAR_Forest_measurableSet_orderedSimplexParams_map_paramValue

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (order : List (Edge V)) :
    MeasurableSet (F.orderedCubeSimplex order) := by
  rw [orderedCubeSimplex]
  exact F.measurableSet_unitCube.inter
    (F.measurableSet_orderedSimplexParams_map_paramValue order measurable_const)
end BKAR.Forest
