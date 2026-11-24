-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.append_mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:19.611796+00:00
-- url     : https://prove2.me/submissions/44d71bfd-911c-4aec-9028-d35c82b54c8c

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
public import Theorems.Thm_BalanceSpecification_FiveSymbol_singleton_four_suffix_forbiddenWord

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {w : Word Alphabet} (hw : w ∈ language shift)
    {a : Alphabet} (ha : a ≠ 4) : w ++ [a] ∈ language shift := by
  apply (mem_language_iff_avoids _).mpr
  intro j hj hocc
  rcases List.infix_concat_iff.mp hocc with hs | hin
  · have hfour := (singleton_four_suffix_forbiddenWord j).trans hs
    exact ha (List.singleton_suffix_append_singleton_iff.mp hfour).symm
  · exact (mem_language_iff_avoids w).mp hw j hj hin
end BalanceSpecification.FiveSymbol
