-- Prove2me | solution 1 for DerivativeChainClusterAnchor.factorial_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:14:24.772472+00:00
-- url     : https://prove2.me/submissions/59f0ab97-0f43-42a1-b74f-bb046e2917eb

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
open Finset
open DerivativeChainClusterAnchor


theorem solution (n m j : ℕ) (hn : 0 < n) (hm : m ≤ n) (hj : j ≤ n) :
    (m.descFactorial j:ℝ)/(n.descFactorial j:ℝ) ≤ ((m:ℝ)/(n:ℝ))^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hjm : j+1 ≤ m
    · have hjn : j < n := by omega
      have hnm : (m:ℝ) ≤ n := by exact_mod_cast hm
      have hnR : (0:ℝ) < n := by exact_mod_cast hn
      have hjR : (0:ℝ) ≤ j := Nat.cast_nonneg j
      have hnj : (0:ℝ) < ((n-j:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hjn
      have hfactor : ((m-j:ℕ):ℝ)/((n-j:ℕ):ℝ) ≤ (m:ℝ)/(n:ℝ) := by
        apply (div_le_div_iff₀ hnj hnR).mpr
        rw [Nat.cast_sub (by omega : j ≤ m),Nat.cast_sub hjn.le]
        nlinarith [mul_le_mul_of_nonneg_left hnm hjR]
      have hrec : (m.descFactorial (j+1):ℝ)/(n.descFactorial (j+1):ℝ) =
          (((m-j:ℕ):ℝ)/((n-j:ℕ):ℝ))*((m.descFactorial j:ℝ)/(n.descFactorial j:ℝ)) := by
        rw [Nat.descFactorial_succ,Nat.descFactorial_succ]
        push_cast
        ring
      rw [hrec]
      calc
        _ ≤ ((m:ℝ)/(n:ℝ))*((m:ℝ)/(n:ℝ))^j :=
          mul_le_mul hfactor (ih (by omega)) (by positivity) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : m < j+1),Nat.cast_zero,zero_div]
      positivity
