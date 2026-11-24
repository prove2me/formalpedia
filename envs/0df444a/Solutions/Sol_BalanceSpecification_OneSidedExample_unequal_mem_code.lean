-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.unequal_mem_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:04.058135+00:00
-- url     : https://prove2.me/submissions/b37db8f7-bbd4-4276-bb20-74f3e34313f4

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
theorem _root_.solution {l m : ℕ} (hm : 1 ≤ m) (hlm : m < l) :
    List.replicate l a ++ List.replicate m b ++ [c] ∈ code :=
  Or.inr (Or.inr ⟨l, m, hm, hlm, rfl⟩)
end BalanceSpecification.OneSidedExample
