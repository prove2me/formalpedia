-- Prove2me | solution 1 for BalanceSpecification.Growth.rate_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:15.636647+00:00
-- url     : https://prove2.me/submissions/cb2fbf86-37a1-4cb3-aad4-41f7b78119f2

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
theorem _root_.solution {a b : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) (hb : ∀ n, 1 ≤ b n)
    (hsa : Submultiplicative a) (hsb : Submultiplicative b)
    (hab : ∀ n, a n ≤ b n) : rate a ≤ rate b := by
  apply le_of_tendsto_of_tendsto (tendsto_rate ha hsa) (tendsto_rate hb hsb)
  exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one (ha n)) (hab n)) (Nat.cast_nonneg n)
end BalanceSpecification.Growth
