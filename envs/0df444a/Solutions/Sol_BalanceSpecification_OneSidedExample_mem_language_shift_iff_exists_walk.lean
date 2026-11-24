-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.mem_language_shift_iff_exists_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:40.447316+00:00
-- url     : https://prove2.me/submissions/d6200799-414c-49fb-947c-a27aab41d6a5

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Theorems.Thm_BalanceSpecification_OneSidedExample_generatedWords_loop
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_mem_language
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_infix
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution {w : Word Alphabet} :
    w ∈ language shift ↔ ∃ s t, Walk s w t := by
  constructor
  · intro hw
    obtain ⟨v, hv, hwv⟩ := language_codedShift_infix_generatedWords hw
    exact (generatedWords_loop hv).infix hwv
  · rintro ⟨s, t, h⟩
    exact h.mem_language
end BalanceSpecification.OneSidedExample
