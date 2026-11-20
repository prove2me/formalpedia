-- Prove2me | solution 1 for DeletionCode.TorusHaar.forall_mem_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:02.830448+00:00
-- url     : https://prove2.me/submissions/92d108ab-00f0-4613-a59c-fc50f8a730aa

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_DeletionCode_TorusHaar
import Theorems.Thm_DeletionCode_TorusHaar_preimage_rectangle

set_option autoImplicit true
open DeletionCode DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] DeletionCode.TorusHaar._p2m_local_instance_196a2ea6bd_18
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.TorusHaar
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume)
    (A : J → Set UnitAddCircle) (hA : ∀ j, MeasurableSet (A j)) :
    μ {x | ∀ j, f x j ∈ A j} = ∏ j, volume (A j) := by
  have hset : {x | ∀ j, f x j ∈ A j} = f ⁻¹' Set.univ.pi A := by
    ext x
    simp
  rw [hset]
  exact preimage_rectangle hf A hA
end DeletionCode.TorusHaar
