-- Prove2me | solution 1 for BalanceSpecification.biBalanced_of_hasVariableSpecification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:03.459045+00:00
-- url     : https://prove2.me/submissions/1b9cb9b4-b442-49d3-8622-150922545fef

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Specification
public import Theorems.Thm_BalanceSpecification_rightBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_leftBalanced_of_hasVariableSpecification

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A]
    {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    (h : HasVariableSpecification X) : BiBalanced (language X) :=
  ⟨rightBalanced_of_hasVariableSpecification hX h,
    leftBalanced_of_hasVariableSpecification hX h⟩
end BalanceSpecification
