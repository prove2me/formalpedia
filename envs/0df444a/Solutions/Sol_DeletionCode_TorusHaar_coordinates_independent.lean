-- Prove2me | solution 1 for DeletionCode.TorusHaar.coordinates_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:34.594168+00:00
-- url     : https://prove2.me/submissions/11f32c4c-3b0f-4bba-880f-baa56d0ec30d

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_DeletionCode_TorusHaar
import Theorems.Thm_DeletionCode_TorusHaar_measurePreserving
import Theorems.Thm_DeletionCode_TorusHaar_coordinates_independent_of_measurePreserving

set_option autoImplicit true
open DeletionCode DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] DeletionCode.TorusHaar._p2m_local_instance_196a2ea6bd_18
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.TorusHaar
theorem _root_.solution
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) :
    iIndepFun (fun j x => f x j) volume :=
  coordinates_independent_of_measurePreserving (measurePreserving f hcont hsurj)
end DeletionCode.TorusHaar
