-- Prove2me | solution 2 for BalanceSpecification.block_chain_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:30.910992+00:00
-- url     : https://prove2.me/submissions/51faa865-34ed-479c-80f6-dde2aead75fc

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
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
open BalanceSpecification
variable {H : ℕ → ℕ → ℝ}
namespace BalanceSpecification
theorem _root_.solution (hzero : ∀ s, H s 0 = 0)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b) (s n k : ℕ) :
    H s (k * n) ≤ ∑ j ∈ Finset.range k, H (s + j * n) n := by
  induction k with
  | zero => simp only [zero_mul, hzero, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ k ih =>
    rw [Nat.add_mul, one_mul, Finset.sum_range_succ]
    exact (hsub s (k * n) n).trans (add_le_add ih le_rfl)
end BalanceSpecification
