-- Prove2me | solution 1 for BalanceSpecification.betaResidual_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:22.510522+00:00
-- url     : https://prove2.me/submissions/861417e7-ad2b-4f28-8dff-a09a7112ba25

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
    betaResidual β a x (n + 1) = β * betaResidual β a x n - betaDigit β a x n := by
  dsimp only [betaResidual, betaDigit]
  split <;> simp only [sub_zero]
end BalanceSpecification
