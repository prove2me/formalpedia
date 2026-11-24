-- Prove2me | solution 1 for BalanceSpecification.Growth.tendsto_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:53:29.9388+00:00
-- url     : https://prove2.me/submissions/fae2f167-a025-4c67-8238-fecffb202033

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
    (hs : Submultiplicative a) :
    Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 (rate a)) := by
  have h := (log_subadditive ha hs).tendsto_lim (log_div_bddBelow ha)
  simpa only [Subadditive.lim, rate] using h
end BalanceSpecification.Growth
