-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.not_synchronized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:50.531685+00:00
-- url     : https://prove2.me/submissions/dfa83ac8-b180-4b1a-bdae-44a509fd2c4e

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_no_synchronizing_word

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution : ¬ Synchronized shift := by
  rintro ⟨_, w, hw⟩
  exact no_synchronizing_word w hw
end BalanceSpecification.FiveSymbol
