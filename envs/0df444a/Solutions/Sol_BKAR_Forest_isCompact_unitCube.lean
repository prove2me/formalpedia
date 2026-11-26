-- Prove2me | solution 1 for BKAR.Forest.isCompact_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:01:53.610986+00:00
-- url     : https://prove2.me/submissions/c514883a-2ca6-4ca9-9ac7-b702662acaac

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
    IsCompact F.unitCube := by
  rw [unitCube]
  exact isCompact_univ_pi fun _ => isCompact_Icc
end BKAR.Forest
