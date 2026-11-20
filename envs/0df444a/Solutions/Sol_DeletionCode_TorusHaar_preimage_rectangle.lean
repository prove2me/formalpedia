-- Prove2me | solution 1 for DeletionCode.TorusHaar.preimage_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:43.705115+00:00
-- url     : https://prove2.me/submissions/8ae28adb-5945-4ed1-8299-5e430187b3fa

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
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume)
    (A : J → Set UnitAddCircle) (hA : ∀ j, MeasurableSet (A j)) :
    μ (f ⁻¹' Set.univ.pi A) = ∏ j, volume (A j) := by
  calc
    μ (f ⁻¹' Set.univ.pi A) = volume (Set.univ.pi A) := by
      have h := congrArg (fun ν : Measure (J → UnitAddCircle) => ν (Set.univ.pi A)) hf.map_eq
      rw [Measure.map_apply hf.measurable (MeasurableSet.univ_pi hA)] at h
      exact h
    _ = ∏ j, volume (A j) := volume_pi_pi A
end DeletionCode.TorusHaar
