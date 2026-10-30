-- Prove2me | solution 1 for DerivativeChainClusterAnchor.integer_block_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:09:20.975345+00:00
-- url     : https://prove2.me/submissions/cfc6823e-d6ae-4536-8e2f-adc4d68940d5

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace DerivativeChainClusterAnchor

theorem integer_block_growth (j : ℕ) (hj : 2 ≤ j) :
    (j:ℝ)^3 ≤ 8*((j:ℝ)-1)*2^(j-2) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hjR : (2:ℝ) ≤ j := by exact_mod_cast hj
    have hpos : 0 < (j:ℝ)-1 := by linarith
    have hpoly : ((j:ℝ)-1)*((j:ℝ)+1)^3 ≤ 2*(j:ℝ)*(j:ℝ)^3 := by
      nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ j) 3)
        (by linarith : (0:ℝ) ≤ (j:ℝ)-2)]
    have hmul := mul_le_mul_of_nonneg_left ih (by positivity : (0:ℝ) ≤ 2*(j:ℝ))
    have hcancel : ((j:ℝ)-1)*((j:ℝ)+1)^3 ≤
        ((j:ℝ)-1)*(16*(j:ℝ)*2^(j-2)) := by nlinarith
    have hnext := (mul_le_mul_iff_right₀ hpos).mp hcancel
    rw [show j+1-2=(j-2)+1 by omega]
    push_cast
    rw [pow_succ (2:ℝ) (j-2)]
    nlinarith only [hnext]

theorem binomial_second_term (j : ℕ) (hj : 2 ≤ j) (v : ℝ) (hv : 0 ≤ v) :
    2^j + ((j:ℝ)*((j:ℝ)-1)/2)*2^(j-2)*v^2 ≤ (2+v)^j := by
  have hs : ({0,2} : Finset ℕ) ⊆ Finset.range (j+1) := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [Finset.mem_range] <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun i _ _ => show 0 ≤ v^i*2^(j-i)*(j.choose i:ℝ) by positivity)
  rw [← add_pow] at hsum
  simpa only [Finset.sum_insert,Finset.mem_singleton,show (0:ℕ) ≠ 2 by decide,
    not_false_eq_true,Finset.sum_singleton,pow_zero,one_mul,Nat.sub_zero,
    Nat.choose_zero_right,Nat.cast_one,mul_one,Nat.cast_choose_two,add_comm v 2,
    mul_assoc,mul_left_comm,mul_comm] using hsum



end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open DerivativeChainClusterAnchor





theorem solution (j : ℕ) (hj : 2 ≤ j) (B : ℝ) (hB : 0 ≤ B) :
    (1+B*(j:ℝ))^((j:ℝ)⁻¹) ≤ 2+4*Real.sqrt B/((j:ℝ)*Real.sqrt (j:ℝ)) := by
  have hj0 : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hsj : 0 < Real.sqrt (j:ℝ) := Real.sqrt_pos.mpr hj0
  let v : ℝ := 4*Real.sqrt B/((j:ℝ)*Real.sqrt (j:ℝ))
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcoef : (j:ℝ)^4/16 ≤ ((j:ℝ)*((j:ℝ)-1)/2)*2^(j-2) := by
    have h := mul_le_mul_of_nonneg_left (_root_.DerivativeChainClusterAnchor.integer_block_growth j hj) hj0.le
    nlinarith
  have hcalc : (j:ℝ)^4/16*v^2=B*(j:ℝ) := by
    dsimp [v]
    rw [div_pow,mul_pow,Real.sq_sqrt hB,mul_pow,Real.sq_sqrt hj0.le]
    field_simp
    ring
  have hpow : 1+B*(j:ℝ) ≤ (2+v)^j := by
    have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg v)
    rw [hcalc] at hc
    have hone : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
    linarith [_root_.DerivativeChainClusterAnchor.binomial_second_term j hj v hv]
  have hroot : ((1+B*(j:ℝ))^((j:ℝ)⁻¹))^j = 1+B*(j:ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hnonneg : 0 ≤ (1+B*(j:ℝ))^((j:ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hright : 0 ≤ 2+v := by positivity
  have hpowers : ((1+B*(j:ℝ))^((j:ℝ)⁻¹))^j ≤ (2+v)^j := by
    rw [hroot]
    exact hpow
  have h := (pow_le_pow_iff_left₀ hnonneg hright (by omega : j ≠ 0)).mp hpowers
  exact h
