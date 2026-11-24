-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.infix_right_of_start_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:45.143672+00:00
-- url     : https://prove2.me/submissions/1b3f4646-cd3d-424c-889c-9d456e3a20b4

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {f u v p q : Word Alphabet}
    (heq : u ++ v = p ++ f ++ q) (hle : u.length ≤ p.length) : f <:+: v := by
  have hprefix : p <+: u ++ v := ⟨f ++ q, by simpa only [List.append_assoc] using heq.symm⟩
  have hshort : u <+: p := List.prefix_of_prefix_length_le
    (List.prefix_append u v) hprefix hle
  obtain ⟨t, ht⟩ := hshort
  refine ⟨t, q, ?_⟩
  apply List.append_cancel_left (as := u)
  calc
    u ++ (t ++ f ++ q) = (u ++ t) ++ f ++ q := by simp only [List.append_assoc]
    _ = p ++ f ++ q := by rw [ht]
    _ = u ++ v := heq.symm
end BalanceSpecification.FiveSymbol
