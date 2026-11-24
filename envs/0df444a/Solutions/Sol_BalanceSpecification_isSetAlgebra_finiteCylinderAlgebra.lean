-- Prove2me | solution 1 for BalanceSpecification.isSetAlgebra_finiteCylinderAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:30.629235+00:00
-- url     : https://prove2.me/submissions/40c31b89-9c2c-46e3-8edb-fcca0f130b45

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Theorems.Thm_BalanceSpecification_centered_block_eq_of_le

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
    IsSetAlgebra (finiteCylinderAlgebra X) where
  empty_mem := ⟨0, by intro x y _; rfl⟩
  compl_mem := by
    rintro E ⟨n, hn⟩
    exact ⟨n, fun x y h => not_congr (hn x y h)⟩
  union_mem := by
    rintro E F ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    intro x y h
    exact or_congr (hn x y (centered_block_eq_of_le (le_max_left _ _) h))
      (hm x y (centered_block_eq_of_le (le_max_right _ _) h))
end BalanceSpecification
