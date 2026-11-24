-- Prove2me | solution 1 for BalanceSpecification.centeredCylinderFamily_subset_finiteCylinderAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:37.26352+00:00
-- url     : https://prove2.me/submissions/17dedcf5-3b8e-4ec2-a0c1-33c740b1d61c

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) :
    centeredCylinderFamily X ⊆ finiteCylinderAlgebra X := by
  rintro E ⟨n, w, hw, rfl⟩
  refine ⟨n, ?_⟩
  intro x y h
  change block x.val (-(n : ℤ)) w.length = w ↔ block y.val (-(n : ℤ)) w.length = w
  rw [hw, h]
end BalanceSpecification
