-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.c_mem_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:40.314521+00:00
-- url     : https://prove2.me/submissions/6c199284-121c-4ed2-98c3-4bc9a2b459ac

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedExample

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution : [c] ∈ code := Or.inl rfl
end BalanceSpecification.OneSidedExample
