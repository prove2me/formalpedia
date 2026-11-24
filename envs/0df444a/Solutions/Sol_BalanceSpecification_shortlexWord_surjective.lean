-- Prove2me | solution 1 for BalanceSpecification.shortlexWord_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:04.930793+00:00
-- url     : https://prove2.me/submissions/15de11dc-6ca3-43d4-a7f0-d04cb22e18cc

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_shortlexWord_eq_getElem

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution : Function.Surjective (shortlexWord (A := A)) := by
  intro w
  have hw : w ∈ shortlexThrough w.length := mem_shortlexThrough.mpr le_rfl
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hw
  exact ⟨j, (shortlexWord_eq_getElem hj).trans he⟩
end BalanceSpecification
