-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.weighted_wordCount_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:27.225386+00:00
-- url     : https://prove2.me/submissions/04e7e9bc-6d47-4fdd-992d-33fbeef2774a

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_arithGeom_partial_sum_le
public import Theorems.Thm_BalanceSpecification_FiveSymbol_wordCount_tail_le

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (n : ℕ) :
    (∑ l ∈ Finset.Icc 1 n, (l : ℝ) * wordCount (language shift) (n - l)) ≤
      (4 / 9 : ℝ) * wordCount (language shift) n := by
  calc
    _ ≤ ∑ l ∈ Finset.Icc 1 n,
        (l : ℝ) * ((1 / 4 : ℝ) ^ l * wordCount (language shift) n) := by
      exact Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left
        (wordCount_tail_le (Finset.mem_Icc.mp hl).2) (Nat.cast_nonneg l))
    _ = (∑ l ∈ Finset.Icc 1 n, (l : ℝ) * (1 / 4 : ℝ) ^ l) *
        wordCount (language shift) n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (arithGeom_partial_sum_le n) (Nat.cast_nonneg _)
end BalanceSpecification.FiveSymbol
