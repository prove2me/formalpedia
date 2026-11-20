-- Prove2me | solution 1 for DeletionCode.CircleUniform.map_realUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:13.518343+00:00
-- url     : https://prove2.me/submissions/de1caaf0-5416-4bb2-a860-cb22fb9e6521

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
import Theorems.Thm_DeletionCode_CircleUniform_measurePreserving_realUnit

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution :
    Measure.map (fun r : ℝ => (r : UnitAddCircle)) realUnit = volume :=
  measurePreserving_realUnit.map_eq
end DeletionCode.CircleUniform
