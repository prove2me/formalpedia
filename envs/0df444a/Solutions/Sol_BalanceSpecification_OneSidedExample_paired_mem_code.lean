-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.paired_mem_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:30.077803+00:00
-- url     : https://prove2.me/submissions/44af9366-bc55-4ca1-b80e-df027bd02171

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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    List.replicate n a ++ List.replicate n b ∈ code := Or.inr (Or.inl ⟨n, hn, rfl⟩)
end BalanceSpecification.OneSidedExample
