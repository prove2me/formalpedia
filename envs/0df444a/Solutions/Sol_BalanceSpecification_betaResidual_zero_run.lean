-- Prove2me | solution 1 for BalanceSpecification.betaResidual_zero_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:04.72408+00:00
-- url     : https://prove2.me/submissions/a9822599-8d89-474e-a575-97ecbb98236d

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
theorem _root_.solution (β a x : ℝ) (m k : ℕ)
    (hzero : ∀ i : ℕ, i < k → betaDigit β a x (m + i) = 0) :
    betaResidual β a x (m + k) = β ^ k * betaResidual β a x m := by
  induction k with
  | zero => simp only [add_zero, pow_zero, one_mul]
  | succ k ih =>
    rw [← Nat.add_assoc, betaResidual_succ, hzero k (Nat.lt_succ_self k), sub_zero,
      ih (fun i hi => hzero i (Nat.lt_succ_of_lt hi)), pow_succ]
    ring
end BalanceSpecification
