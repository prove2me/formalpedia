-- Prove2me | solution 1 for BKAR.Forest.measurableSet_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:00.680928+00:00
-- url     : https://prove2.me/submissions/f28e7e32-fe8c-4784-af87-0c41cc903bfa

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    MeasurableSet F.unitCube := by
  rw [unitCube]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
end BKAR.Forest
