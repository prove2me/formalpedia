-- Prove2me | solution 1 for BalanceSpecification.sum_quarter_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:42.208253+00:00
-- url     : https://prove2.me/submissions/ce9d16d7-de04-450d-87fc-d4796a88ead2

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (N : ℕ) :
    (∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ (n + 1)) ≤ 1 / 3 := by
  have hformula : ∀ N : ℕ, (∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ (n + 1)) =
      1 / 3 - (1 / 3) * ((1 : ℝ) / 4) ^ N := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [hformula]
  exact sub_le_self _ (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
end BalanceSpecification
