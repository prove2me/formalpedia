-- Prove2me | solution 1 for BalanceSpecification.Growth.le_mul_exp_rate_of_bsm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:19.402813+00:00
-- url     : https://prove2.me/submissions/b8e6b401-70b2-4e95-8b0f-aea26aaa08a8

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
    (hs : Submultiplicative a) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ m n, a m * a n ≤ c * a (m + n)) (n : ℕ) :
    a n ≤ c * Real.exp ((n : ℝ) * rate a) := by
  have hp i : 0 < a i := lt_of_lt_of_le zero_lt_one (ha i)
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.zero_add, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one] using
      (mul_le_mul_iff_left₀ (hp 0)).mp (by simpa only [Nat.zero_add, mul_comm c] using hb 0 0)
  let u : ℕ → ℝ := fun k => -Real.log (a k) + Real.log c
  have hu : Subadditive u := by
    intro m k
    have H := Real.log_le_log (mul_pos (hp m) (hp k)) (hb m k)
    rw [Real.log_mul (hp m).ne' (hp k).ne',
      Real.log_mul hcp.ne' (hp (m + k)).ne'] at H
    dsimp only [u]
    linarith only [H]
  have ht : Tendsto (fun k : ℕ => u k / k) atTop (𝓝 (-rate a)) := by
    have H := (tendsto_rate ha hs).neg.add
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log c))
    simpa only [u, add_div, neg_div, add_zero] using H
  have hlim : hu.lim = -rate a := tendsto_nhds_unique
    (hu.tendsto_lim ht.bddBelow_range) ht
  have H := hu.lim_le_div ht.bddBelow_range hn
  rw [hlim] at H
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have H' := (le_div_iff₀ hnp).mp H
  have hlog : Real.log (a n) ≤ Real.log c + (n : ℝ) * rate a := by
    dsimp only [u] at H'
    linarith only [H']
  calc
    a n = Real.exp (Real.log (a n)) := (Real.exp_log (hp n)).symm
    _ ≤ Real.exp (Real.log c + (n : ℝ) * rate a) := Real.exp_le_exp.mpr hlog
    _ = c * Real.exp ((n : ℝ) * rate a) := by rw [Real.exp_add, Real.exp_log hcp]
end BalanceSpecification.Growth
