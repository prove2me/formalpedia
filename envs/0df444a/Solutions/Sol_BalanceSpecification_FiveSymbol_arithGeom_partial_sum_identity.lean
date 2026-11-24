-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.arithGeom_partial_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:44.316277+00:00
-- url     : https://prove2.me/submissions/b943d993-d726-4a5c-9ac7-ad44a719bb0b

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (n : ℕ) :
    9 * (∑ l ∈ Finset.range (n + 1), (l : ℝ) * (1 / 4 : ℝ) ^ l) =
      4 - (3 * (n : ℝ) + 4) * (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    push_cast
    nlinarith only [ih]
end BalanceSpecification.FiveSymbol
