-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.no_synchronizing_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:02.2516+00:00
-- url     : https://prove2.me/submissions/7297d814-b516-44ee-9430-9e057ac710cc

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_not_isSynchronizing_of_ne_nil
public import Theorems.Thm_BalanceSpecification_FiveSymbol_singleton_zero_mem_language
public import Theorems.Thm_BalanceSpecification_IsSynchronizing_of_infix
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (w : Word Alphabet) : ¬ IsSynchronizing (language shift) w := by
  intro hsync
  by_cases hw : w = []
  · subst w
    have hzero := hsync.of_infix (language_factorial shift) singleton_zero_mem_language List.nil_infix
    exact not_isSynchronizing_of_ne_nil singleton_zero_mem_language (by decide) hzero
  · exact not_isSynchronizing_of_ne_nil hsync.1 hw hsync
end BalanceSpecification.FiveSymbol
