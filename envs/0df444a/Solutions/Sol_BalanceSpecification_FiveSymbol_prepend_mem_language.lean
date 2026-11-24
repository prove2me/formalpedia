-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.prepend_mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:08.837389+00:00
-- url     : https://prove2.me/submissions/e9f0b4c9-260f-43a0-b5a8-b3953480104d

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
public import Theorems.Thm_BalanceSpecification_FiveSymbol_singleton_zero_prefix_forbiddenWord

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {w : Word Alphabet} (hw : w ∈ language shift)
    {a : Alphabet} (ha : a ≠ 0) : a :: w ∈ language shift := by
  apply (mem_language_iff_avoids _).mpr
  intro j hj hocc
  rcases List.infix_cons_iff.mp hocc with hs | hin
  · have hzero := (singleton_zero_prefix_forbiddenWord j).trans hs
    exact ha (List.singleton_prefix_cons_iff.mp hzero).symm
  · exact (mem_language_iff_avoids w).mp hw j hj hin
end BalanceSpecification.FiveSymbol
