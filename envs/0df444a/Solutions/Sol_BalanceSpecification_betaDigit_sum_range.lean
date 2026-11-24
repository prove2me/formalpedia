-- Prove2me | solution 1 for BalanceSpecification.betaDigit_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:42.643876+00:00
-- url     : https://prove2.me/submissions/cf783371-e13d-419f-a0ab-b3ffd39838ce

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Theorems.Thm_BalanceSpecification_betaResidual_succ

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β a x : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, betaDigit β a x i / β ^ (i + 1)) =
      x - betaResidual β a x n / β ^ n := by
  induction n with
  | zero => simp only [Finset.sum_range_zero, betaResidual, pow_zero, div_one, sub_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, betaResidual_succ, pow_succ]
    field_simp
    ring
end BalanceSpecification
