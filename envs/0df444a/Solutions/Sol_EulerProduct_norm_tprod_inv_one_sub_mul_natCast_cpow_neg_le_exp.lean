-- Prove2me | solution 1 for EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d7c1f505-9ada-5b6b-a32e-78da686fda4f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp

set_option autoImplicit false

open Complex

namespace R4EulerDom

theorem norm_tprod_inv_one_sub_eq_exp {ι : Type*} (a : ι → ℂ) (ha : Summable fun i => ‖a i‖)
    (ha1 : ∀ i, ‖a i‖ < 1) :
    ‖∏' i, (1 - a i)⁻¹‖ = Real.exp (∑' i, (-log (1 - a i)).re) := by
  have hne : ∀ i, 1 - a i ≠ 0 := fun i h => by
    have : a i = 1 := (sub_eq_zero.mp h).symm
    have := ha1 i
    rw [‹a i = 1›, norm_one] at this
    exact lt_irrefl _ this
  have hsum : Summable fun i => -log (1 - a i) := ha.of_norm.clog_one_sub.neg
  have H := hsum.hasSum.cexp.tprod_eq
  have hcongr : (cexp ∘ fun i => -log (1 - a i)) = fun i => (1 - a i)⁻¹ := by
    funext i
    simp only [Function.comp_apply, exp_neg, exp_log (hne i)]
  rw [hcongr] at H
  rw [H, norm_exp, re_tsum hsum]

theorem norm_neg_log_one_sub_le {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) : ‖-log (1 - a)‖ ≤ 2 * ‖a‖ := by
  rw [norm_neg, sub_eq_add_neg]
  have h := Complex.norm_log_one_add_half_le_self (z := -a) (by rwa [norm_neg])
  rw [norm_neg] at h
  linarith [norm_nonneg a]

theorem norm_natCast_cpow_neg (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [norm_natCast_cpow_of_pos hn]; simp

theorem main {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) := by
  have hN0 : ∀ i, 0 < N i := fun i => by have := hN i; omega
  set a : ι → ℂ := fun i => c i * ((N i : ℕ) : ℂ) ^ (-s) with ha_def
  have ha_le : ∀ i, ‖a i‖ ≤ ((N i : ℕ) : ℝ) ^ (-s.re) := fun i => by
    show ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, norm_natCast_cpow_neg _ (hN0 i)]
    calc ‖c i‖ * ((N i : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((N i : ℕ) : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hc i) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := one_mul _
  have hpow_half : ∀ i, ((N i : ℕ) : ℝ) ^ (-s.re) ≤ 1 / 2 := fun i => by
    have h2 : (2 : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hN i
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    have h1 : (2 : ℝ) ≤ ((N i : ℕ) : ℝ) ^ s.re := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ s.re := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
        _ ≤ ((N i : ℕ) : ℝ) ^ s.re := Real.rpow_le_rpow (by norm_num) h2 (by linarith)
    rw [one_div]
    exact inv_anti₀ (by norm_num) h1
  have ha_half : ∀ i, ‖a i‖ ≤ 1 / 2 := fun i => (ha_le i).trans (hpow_half i)
  have ha_lt : ∀ i, ‖a i‖ < 1 := fun i => (ha_half i).trans_lt (by norm_num)
  have ha_sum : Summable fun i => ‖a i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) ha_le hsum
  rw [show (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) = fun i => (1 - a i)⁻¹ from rfl,
    norm_tprod_inv_one_sub_eq_exp a ha_sum ha_lt, Real.exp_le_exp]

  have hlog_le : ∀ i, ‖-log (1 - a i)‖ ≤ 2 * ((N i : ℕ) : ℝ) ^ (-s.re) := fun i =>
    (norm_neg_log_one_sub_le (ha_half i)).trans (by linarith [ha_le i])
  have hlog_sum : Summable fun i => ‖-log (1 - a i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hlog_le (hsum.mul_left 2)
  have hre_sum : Summable fun i => (-log (1 - a i)).re :=
    (hlog_sum.of_norm).mapL Complex.reCLM
  calc ∑' i, (-log (1 - a i)).re ≤ ∑' i, ‖-log (1 - a i)‖ :=
        Summable.tsum_le_tsum (fun i => (re_le_norm _)) hre_sum hlog_sum
    _ ≤ ∑' i, 2 * ((N i : ℕ) : ℝ) ^ (-s.re) :=
        Summable.tsum_le_tsum hlog_le hlog_sum (hsum.mul_left 2)
    _ = 2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re) := tsum_mul_left

end R4EulerDom

theorem solution
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) :=
  R4EulerDom.main N hN c hc s hs hsum

end S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
end P2MW
export P2MW.S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp (solution)
