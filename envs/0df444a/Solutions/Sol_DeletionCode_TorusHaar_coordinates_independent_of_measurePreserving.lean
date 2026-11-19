-- Prove2me | solution 1 for DeletionCode.TorusHaar.coordinates_independent_of_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:19.156971+00:00
-- url     : https://prove2.me/submissions/8f34ec9d-9f43-43ea-b84a-42479f85ad83

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_DeletionCode_TorusHaar
import Theorems.Thm_DeletionCode_TorusHaar_coordinate_measurePreserving_of_measurePreserving

set_option autoImplicit true
open DeletionCode DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] DeletionCode.TorusHaar._p2m_local_instance_196a2ea6bd_18
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.TorusHaar
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume) :
    iIndepFun (fun j x => f x j) μ := by
  have : IsProbabilityMeasure (μ.map f) := by
    rw [hf.map_eq]
    infer_instance
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_of_map f
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (coordinate_measurePreserving_of_measurePreserving hf j).aemeasurable)).2
  have hcoords (j : J) : μ.map (fun x => f x j) = volume :=
    (coordinate_measurePreserving_of_measurePreserving hf j).map_eq
  simp_rw [hcoords]
  exact hf.map_eq
end DeletionCode.TorusHaar
