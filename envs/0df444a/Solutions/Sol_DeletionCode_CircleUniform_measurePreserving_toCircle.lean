-- Prove2me | solution 1 for DeletionCode.CircleUniform.measurePreserving_toCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:44:13.031469+00:00
-- url     : https://prove2.me/submissions/4c582433-8421-477f-aef4-93373ba393b7

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
theorem _root_.solution (I : Type*) [Fintype I] :
    MeasurePreserving (@toCircle I) (realWeights I) volume := by
  exact measurePreserving_pi (fun _ : I => realUnit)
    (fun _ : I => (volume : Measure UnitAddCircle)) (fun _ => measurePreserving_realUnit)
end DeletionCode.CircleUniform
