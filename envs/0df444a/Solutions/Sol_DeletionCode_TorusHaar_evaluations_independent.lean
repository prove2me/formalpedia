-- Prove2me | solution 1 for DeletionCode.TorusHaar.evaluations_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:11.616918+00:00
-- url     : https://prove2.me/submissions/84c7ff47-97bf-4f83-9c6f-5e5dcea95b4b

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_DeletionCode_TorusHaar

set_option autoImplicit true
open DeletionCode DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] DeletionCode.TorusHaar._p2m_local_instance_196a2ea6bd_18
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.TorusHaar
theorem _root_.solution :
    iIndepFun (fun i (x : I → UnitAddCircle) => x i) volume := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
end DeletionCode.TorusHaar
