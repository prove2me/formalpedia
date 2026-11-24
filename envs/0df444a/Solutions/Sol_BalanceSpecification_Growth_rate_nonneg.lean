-- Prove2me | solution 1 for BalanceSpecification.Growth.rate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:22.213804+00:00
-- url     : https://prove2.me/submissions/968a6a7a-569e-459a-87ed-a0a4848add43

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
public import Theorems.Thm_BalanceSpecification_Growth_tendsto_rate

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) : 0 ≤ rate a := by
  exact ge_of_tendsto' (tendsto_rate ha hs) fun n =>
    div_nonneg (Real.log_nonneg (ha n)) (Nat.cast_nonneg n)
end BalanceSpecification.Growth
