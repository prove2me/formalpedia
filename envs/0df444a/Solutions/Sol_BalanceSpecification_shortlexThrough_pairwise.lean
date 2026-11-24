-- Prove2me | solution 1 for BalanceSpecification.shortlexThrough_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:24.416809+00:00
-- url     : https://prove2.me/submissions/6aa2ce27-63b3-4cdf-9071-2692f89b4897

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_lexWords_shortlex
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
namespace BalanceSpecification
theorem _root_.solution (n : ℕ) :
    (shortlexThrough (A := A) n).Pairwise (List.Shortlex (· < ·)) := by
  induction n with
  | zero => simpa only [shortlexThrough, Nat.zero_add, List.range_one, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using lexWords_shortlex (A := A) 0
  | succ n ih =>
    rw [shortlexThrough_succ, List.pairwise_append]
    refine ⟨ih, lexWords_shortlex _, ?_⟩
    intro u hu v hv
    apply List.Shortlex.of_length_lt
    have hu := mem_shortlexThrough.mp hu
    have hv := mem_lexWords.mp hv
    omega
end BalanceSpecification
