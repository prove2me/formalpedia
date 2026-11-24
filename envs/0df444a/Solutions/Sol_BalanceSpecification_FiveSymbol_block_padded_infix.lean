-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.block_padded_infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:43.139794+00:00
-- url     : https://prove2.me/submissions/de4fd4c4-4829-40ce-a604-efdc27ab55e4

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_padded_at_nat
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
theorem _root_.solution (w : Word Alphabet) {k : ℤ} {n : ℕ}
    (hk : 0 ≤ k) (hend : k + (n : ℤ) ≤ w.length) :
    block (padded w) k n <:+: w := by
  let a := k.toNat
  have ha : (a : ℤ) = k := Int.toNat_of_nonneg hk
  have halen : a + n ≤ w.length := by omega
  have heq : block (padded w) k n = (w.drop a).take n := by
    apply List.ext_getElem
    · simp only [length_block, List.length_take, List.length_drop]
      omega
    · intro i hi _
      have hin : i < n := by simpa only [length_block] using hi
      have hai : a + i < w.length := by omega
      simp only [block, List.getElem_ofFn, List.getElem_take, List.getElem_drop]
      have hki : k + (i : ℤ) = ((a + i : ℕ) : ℤ) := by omega
      rw [hki]
      exact padded_at_nat w hai
  rw [heq]
  exact (List.take_prefix n (w.drop a)).isInfix.trans (List.drop_suffix a w).isInfix
end BalanceSpecification.FiveSymbol
