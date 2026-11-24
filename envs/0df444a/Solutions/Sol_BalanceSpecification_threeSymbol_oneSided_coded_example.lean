-- Prove2me | solution 1 for BalanceSpecification.threeSymbol_oneSided_coded_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:39.7307+00:00
-- url     : https://prove2.me/submissions/290ee248-ae75-4e0d-86fd-dc6e11615c4a

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Definitions.Def_BalanceSpecificaton_Examples
public import Theorems.Thm_BalanceSpecification_FiveSymbol_irreducible
public import Theorems.Thm_BalanceSpecification_OneSidedExample_entropy_eq_log_two
public import Theorems.Thm_BalanceSpecification_OneSidedExample_irreducible
public import Theorems.Thm_BalanceSpecification_OneSidedExample_nonempty
public import Theorems.Thm_BalanceSpecification_OneSidedExample_one_sided_example_properties


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution :
    IsCoded OneSidedExample.shift ∧ Irreducible OneSidedExample.shift ∧
      entropy OneSidedExample.shift OneSidedExample.nonempty = Real.log 2 ∧
      RightBalanced (language OneSidedExample.shift) ∧
      ¬LeftBalanced (language OneSidedExample.shift) ∧
      ¬HasVariableSpecification OneSidedExample.shift :=
  ⟨⟨OneSidedExample.code, rfl⟩, OneSidedExample.irreducible,
    OneSidedExample.entropy_eq_log_two, OneSidedExample.one_sided_example_properties⟩
end BalanceSpecification
