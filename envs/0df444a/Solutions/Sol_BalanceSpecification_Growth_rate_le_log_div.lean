-- Prove2me | solution 1 for BalanceSpecification.Growth.rate_le_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:53:30.795126+00:00
-- url     : https://prove2.me/submissions/59b1f126-5d79-4278-9975-ca8568ca67d1

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
public import Theorems.Thm_BalanceSpecification_Growth_log_subadditive
public import Theorems.Thm_BalanceSpecification_Growth_log_div_bddBelow

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) {n : ℕ} (hn : n ≠ 0) :
    rate a ≤ Real.log (a n) / n := by
  have h := (log_subadditive ha hs).lim_le_div (log_div_bddBelow ha) hn
  simpa only [Subadditive.lim, rate] using h
end BalanceSpecification.Growth
