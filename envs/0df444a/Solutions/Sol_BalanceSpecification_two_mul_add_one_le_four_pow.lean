-- Prove2me | solution 1 for BalanceSpecification.two_mul_add_one_le_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:32.225678+00:00
-- url     : https://prove2.me/submissions/0e1fdb39-48a9-4d6f-94c0-4c42aaf609a1

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
theorem _root_.solution (n : ℕ) : 2 * n + 1 ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega
end BalanceSpecification
