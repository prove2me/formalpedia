-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.one_sided_example_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:31.16261+00:00
-- url     : https://prove2.me/submissions/a4b323ac-c198-4d6c-87e8-a552ad034511

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_rightBalanced
public import Theorems.Thm_BalanceSpecification_OneSidedExample_not_leftBalanced
public import Theorems.Thm_BalanceSpecification_OneSidedExample_not_hasVariableSpecification

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution :
    RightBalanced (language shift) ∧ ¬ LeftBalanced (language shift) ∧
      ¬ HasVariableSpecification shift :=
  ⟨rightBalanced, not_leftBalanced, not_hasVariableSpecification⟩
end BalanceSpecification.OneSidedExample
