-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.arithGeom_partial_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:05.900667+00:00
-- url     : https://prove2.me/submissions/aa925f9b-d6a3-4f6e-b3ed-296891a0ac6a

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_arithGeom_partial_sum_identity

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (n : ℕ) :
    (∑ l ∈ Finset.Icc 1 n, (l : ℝ) * (1 / 4 : ℝ) ^ l) ≤ 4 / 9 := by
  have hsub : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro l hl
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hl).2; omega)
  have H : (∑ l ∈ Finset.Icc 1 n, (l : ℝ) * (1 / 4 : ℝ) ^ l) ≤
      ∑ l ∈ Finset.range (n + 1), (l : ℝ) * (1 / 4 : ℝ) ^ l :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun l _ _ => mul_nonneg (Nat.cast_nonneg l) (pow_nonneg (by norm_num) l))
  have htail : 0 ≤ (3 * (n : ℝ) + 4) * (1 / 4 : ℝ) ^ n :=
    mul_nonneg (by positivity) (pow_nonneg (by norm_num) n)
  have hid := arithGeom_partial_sum_identity n
  linarith only [H, htail, hid]
end BalanceSpecification.FiveSymbol
