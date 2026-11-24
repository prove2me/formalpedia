-- Prove2me | solution 1 for BalanceSpecification.block_subword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:25.12918+00:00
-- url     : https://prove2.me/submissions/4bd544a4-0a8b-47d4-a3e4-bb72c5ed9472

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Language
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.getElem_block

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {A : Type*} (x : Configuration A) (k : ℤ)
    (p u q : Word A) (h : block x k (p ++ u ++ q).length = p ++ u ++ q) :
    block x (k + p.length) u.length = u := by
  apply List.ext_getElem
  · simp only [length_block]
  · intro i hi hi'
    have hindex : p.length + i < (p ++ u ++ q).length := by
      simp only [List.length_append]
      omega
    have he := List.getElem_of_eq h (show p.length + i <
      (block x k (p ++ u ++ q).length).length by simpa only [length_block] using hindex)
    simp only [block, List.getElem_ofFn] at he
    simp only [List.append_assoc] at he
    simp only [List.getElem_append_right (show p.length ≤ p.length + i by omega),
      Nat.add_sub_cancel_left, List.getElem_append_left hi'] at he
    simp only [block, List.getElem_ofFn]
    simpa only [Nat.cast_add, add_assoc] using he
end BalanceSpecification
