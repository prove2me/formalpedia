-- Prove2me | solution 1 for BalanceSpecification.betaDigit_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:50.214704+00:00
-- url     : https://prove2.me/submissions/3ec79b75-5c84-4dc7-844f-9309f8581e31

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (β a x : ℝ) (n : ℕ) :
    betaDigit β a x n = 0 ∨ betaDigit β a x n = 1 := by
  unfold betaDigit
  split <;> simp only [or_true, true_or]
end BalanceSpecification
