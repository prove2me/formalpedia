-- Prove2me | solution 1 for DeletionCode.CircleUniform.measurePreserving_realUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:43:00.102197+00:00
-- url     : https://prove2.me/submissions/1af186f7-8d16-4403-a5d0-a20e88a21cd2

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution :
    MeasurePreserving (fun r : ℝ => (r : UnitAddCircle)) realUnit volume := by
  unfold realUnit
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa only [zero_add] using UnitAddCircle.measurePreserving_mk 0
end DeletionCode.CircleUniform
