-- Prove2me | solution 1 for DerivativeChainContinuation.positive_weighted_single_radius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:34:51.810302+00:00
-- url     : https://prove2.me/submissions/deb5a868-59d2-4f40-a1f8-e87d35af5461

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem nat_two_power_strict (k : ℕ) (hk : 2 ≤ k) : k+1<2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega





end DerivativeChainContinuation

theorem solution (s k : ℕ) (hk : 2 ≤ k) (b t : ℝ)
    (ht : 0<t)
    (hroot : (positiveWeighted s k (X-C b)).eval t=0) : b<(2 : ℝ)^k*t := by
  have he : ((s : ℝ)+(k : ℝ))*t=(s : ℝ)*b := by
    simp only [positiveWeighted,derivative_X_sub_C,eval_add,eval_mul,eval_C,eval_X,
      eval_sub,mul_one] at hroot
    nlinarith
  have hs : 1 ≤ s := by
    by_contra hn
    have hz : s=0 := by omega
    subst s
    norm_num at he
    rcases he with hkk | htt
    · omega
    · linarith
  have hnat : s+k<2^k*s := by
    have hp := nat_two_power_strict k hk
    have hmult := Nat.mul_lt_mul_of_pos_right hp (show 0<s by omega)
    nlinarith
  have hcast : (s : ℝ)+(k : ℝ)<(2 : ℝ)^k*(s : ℝ) := by exact_mod_cast hnat
  have hmul := mul_lt_mul_of_pos_right hcast ht
  have hspos : 0<(s : ℝ) := by exact_mod_cast (show 0<s by omega)
  nlinarith
