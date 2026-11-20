-- Prove2me | solution 1 for BooleanFun.BV.probabilityCondorcetWinner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:14:17.771475+00:00
-- url     : https://prove2.me/submissions/c6dc19cf-2ffa-480d-89fe-9a1cf1b2c47e

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
import Theorems.Thm_BooleanFun_BV_VoteConsistent_comm_right
import Theorems.Thm_BooleanFun_BV_VoteConsistent_comm_rcyc
import Theorems.Thm_BooleanFun_BV_oneOn_NAE3_eq
import Theorems.Thm_BooleanFun_BV__triple_sum_oneOn_consistent_eq
import Theorems.Thm_BooleanFun_BV__eq_noise_operator

set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
local notation "T" => _Tnae3
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) :
    probabilityCondorcetWinner f = 3/4 * (1- noise_stability (-1/3) f) := by
  simp_rw [probabilityCondorcetWinner.eq_def, oneOn_NAE3_eq hbv, sub_mul, sum_sub_distrib]
  conv => enter [1, 2, 1, 1, 1]; tactic => simp_rw [← mul_sum]
  rw [_triple_sum_oneOn_consistent_eq]
  conv => enter [1, 2, 2, 2, x]; rw [sum_comm]; enter [2, y, 2, z];
          rw [VoteConsistent.comm_right]
  conv => enter [1, 2, 1, 2]; rw [sum_comm]; enter [2, x]; rw [sum_comm];
          enter [2, y, 2, z]; rw [VoteConsistent.comm_rcyc]
  rw [sub_sub, sub_sub, ← two_mul]
  nth_rewrite 1 [← one_mul (∑ x, _)]
  rw [← add_mul]
  conv => enter [1, 2, 2, 2, 2, x, 2, y, 2, z]; rw [mul_assoc, mul_assoc]
  conv => enter [1, 2, 2, 2]; tactic => simp_rw [← mul_sum]
  -- rewrite in terms of T and apply main lemma `_eq_noise_operator`
  have : ∑ x, f x * ∑ y, f y * ∑ z, oneOn (VoteConsistent x y z)
      = 6^n * noise_stability (-1/3) f := by
    calc
      _ = 3^n * (1/3)^n * ∑ x, f x * ∑ y, f y * ∑ z, oneOn (VoteConsistent x y z) := by simp only [one_div,
          inv_pow, isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff',
          OfNat.ofNat_ne_zero, false_and, not_false_eq_true, IsUnit.mul_inv_cancel, one_mul]
      _ = 3^n * ∑ x, f x * T f x := by rw [mul_assoc, mul_sum]; conv => {enter [1, 2, 2, x]; rw [← mul_assoc, mul_comm _ (f x), mul_assoc]}; rfl
      _ = 3^n * 2^n * (1/2)^n * ∑ x, f x * T f x := by simp only [LinearMap.coe_mk, one_div, inv_pow,
          sum_boole, AddHom.coe_mk, isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
          false_and, not_false_eq_true, IsUnit.mul_inv_cancel_right]
      _ = 6^n * (1/2)^n * ∑ x, f x * T f x := by congr; rw [← mul_pow]; congr; norm_num
      _ = 6^n * ⟪f, T f⟫ := by rw [mul_assoc]; rfl
      _ = 6^n * ⟪f, noise_operator (-1/3) f⟫ := by rw [_eq_noise_operator]
  rw [this]
  have hpow : (1 / 6 : ℝ) ^ n * 6 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp -- todo : speedup
  rw [hpow]
  ring
end BooleanFun.BV
