-- Prove2me | solution 1 for DerivativeChainClusterAnchor.finite_block_summability
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T22:46:56.974529+00:00
-- url     : https://prove2.me/submissions/6c02a6a8-6fe4-45c2-94b7-0de7eea988f4

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





theorem reciprocal_sqrt_step (j : ℕ) (hj : 2 ≤ j) :
    1/((j:ℝ)*Real.sqrt (j:ℝ)) ≤
      2*(1/Real.sqrt ((j-1:ℕ):ℝ)-1/Real.sqrt (j:ℝ)) := by
  have hjR : (2:ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0:ℝ) < j := by linarith
  have hprev : (0:ℝ) < ((j-1:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < j-1)
  have ha : 0 < Real.sqrt (j:ℝ) := Real.sqrt_pos.mpr hj0
  have hb : 0 < Real.sqrt ((j-1:ℕ):ℝ) := Real.sqrt_pos.mpr hprev
  have hsqA : (Real.sqrt (j:ℝ))^2=(j:ℝ) := Real.sq_sqrt hj0.le
  have hsqB : (Real.sqrt ((j-1:ℕ):ℝ))^2=(j:ℝ)-1 := by
    rw [Real.sq_sqrt hprev.le,Nat.cast_sub (by omega : 1 ≤ j),Nat.cast_one]
  have hsq : (((2:ℝ)*(j:ℝ)+1)*Real.sqrt ((j-1:ℕ):ℝ))^2 ≤
      ((2:ℝ)*(j:ℝ)*Real.sqrt (j:ℝ))^2 := by
    rw [mul_pow,mul_pow,hsqB,hsqA]
    nlinarith
  have hlin := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have he : 2*(1/Real.sqrt ((j-1:ℕ):ℝ)-1/Real.sqrt (j:ℝ)) =
      (2*(Real.sqrt (j:ℝ)-Real.sqrt ((j-1:ℕ):ℝ)))/
        (Real.sqrt ((j-1:ℕ):ℝ)*Real.sqrt (j:ℝ)) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hj0 ha) (mul_pos hb ha)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlin ha.le]



end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open DerivativeChainClusterAnchor







theorem solution (N : ℕ) :
    (∑ j ∈ Finset.range N, 1/((j+2:ℝ)*Real.sqrt (j+2:ℝ))) ≤ 2 := by
  have hsum : (∑ j ∈ Finset.range N, 1/((j+2:ℝ)*Real.sqrt (j+2:ℝ))) ≤
      2*(1-1/Real.sqrt (N+1:ℝ)) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := _root_.DerivativeChainClusterAnchor.reciprocal_sqrt_step (N+2) (by omega)
      simp only [show N+2-1=N+1 by omega,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hs
      push_cast
      norm_num only [add_assoc]
      linarith
  have hn : 0 ≤ 1/Real.sqrt (N+1:ℝ) := by positivity
  linarith
