-- Prove2me | solution 1 for DeletionCode.CircleUniform.map_toCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:14.043836+00:00
-- url     : https://prove2.me/submissions/c9f09029-32c8-4c06-b4b9-64adb97fb301

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
import Theorems.Thm_DeletionCode_CircleUniform_measurePreserving_toCircle

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution (I : Type*) [Fintype I] :
    Measure.map (@toCircle I) (realWeights I) = volume :=
  (measurePreserving_toCircle I).map_eq
end DeletionCode.CircleUniform
