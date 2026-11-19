-- Prove2me | solution 1 for DeletionCode.TorusHaar.coordinate_measurePreserving_of_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:36:21.769252+00:00
-- url     : https://prove2.me/submissions/0d720e05-512c-4361-98fb-6d1a8f72896c

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
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume) (j : J) :
    MeasurePreserving (fun x => f x j) μ volume :=
  (measurePreserving_eval (fun _ : J => (volume : Measure UnitAddCircle)) j).comp hf
end DeletionCode.TorusHaar
