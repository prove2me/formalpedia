-- Prove2me | solution 1 for DeletionCode.TorusHaar.coordinate_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:34.064832+00:00
-- url     : https://prove2.me/submissions/0b3c4252-0cd4-4fbd-9689-431d3d17ee07

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_DeletionCode_TorusHaar
import Theorems.Thm_DeletionCode_TorusHaar_measurePreserving
import Theorems.Thm_DeletionCode_TorusHaar_coordinate_measurePreserving_of_measurePreserving

set_option autoImplicit true
open DeletionCode DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] DeletionCode.TorusHaar._p2m_local_instance_196a2ea6bd_18
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.TorusHaar
theorem _root_.solution
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) (j : J) :
    MeasurePreserving (fun x => f x j) volume volume :=
  coordinate_measurePreserving_of_measurePreserving (measurePreserving f hcont hsurj) j
end DeletionCode.TorusHaar
