-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:27.592887+00:00
-- url     : https://prove2.me/submissions/050cb01b-f171-4308-9bda-b4681a1301ca

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Theorems.Thm_BalanceSpecification_codedShift_irreducible


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution : Irreducible shift := codedShift_irreducible code
end BalanceSpecification.OneSidedExample
