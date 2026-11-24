-- Prove2me | solution 1 for BalanceSpecification.Growth.exp_mul_rate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:12.111432+00:00
-- url     : https://prove2.me/submissions/7f3d60df-0df2-40d3-9487-ba733f8bceb8

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
public import Theorems.Thm_BalanceSpecification_Growth_rate_le_log_div

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) (n : ℕ) :
    Real.exp ((n : ℝ) * rate a) ≤ a n := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, zero_mul, Real.exp_zero] using ha 0
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h := (le_div_iff₀ hnp).mp (rate_le_log_div ha hs hn)
  calc
    Real.exp ((n : ℝ) * rate a) ≤ Real.exp (Real.log (a n)) :=
      Real.exp_le_exp.mpr (by simpa only [mul_comm] using h)
    _ = a n := Real.exp_log (lt_of_lt_of_le zero_lt_one (ha n))
end BalanceSpecification.Growth
