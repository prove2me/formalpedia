-- Prove2me | solution 1 for BalanceSpecification.measurableSet_of_mem_finiteCylinderAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:42.953809+00:00
-- url     : https://prove2.me/submissions/f6a99cfc-bcdc-4f63-ab09-997215b7aadd

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Theorems.Thm_BalanceSpecification_exists_centered_cylinder_union
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} {E : Set X.carrier}
    (hE : E ∈ finiteCylinderAlgebra X) : MeasurableSet E := by
  obtain ⟨n, S, _, rfl⟩ := exists_centered_cylinder_union hE
  exact S.measurableSet_biUnion (fun w _ => measurableSet_cylinder X w (-(n : ℤ)))
end BalanceSpecification
