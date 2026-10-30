-- Prove2me | solution 1 for DerivativeChainPhaseLock.cluster_moment_error
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:17:21.995891+00:00
-- url     : https://prove2.me/submissions/9675f6ae-dbe5-49c7-b6e2-cc5840b27319

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_MomentErrorBounds
import Definitions.Def_DerivativeChainAnalytic_OddMomentPersistence
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace DerivativeChainPhaseLock
noncomputable section




theorem norm_power_perturbation (q : ℕ) (a z : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hz : ‖z-a‖ ≤ ε*‖a‖) :
    ‖z^q-a^q‖ ≤ ((1+ε)^q-1)*‖a‖^q := by
  have hza : ‖z‖ ≤ (1+ε)*‖a‖ := by
    calc
      ‖z‖ = ‖(z-a)+a‖ := by congr 1; ring
      _ ≤ ‖z-a‖+‖a‖ := norm_add_le _ _
      _ ≤ (1+ε)*‖a‖ := by linarith
  induction q with
  | zero => simp
  | succ q ih =>
    have hp : ‖z‖^q ≤ ((1+ε)*‖a‖)^q := pow_le_pow_left₀ (norm_nonneg _) hza q
    calc
      ‖z^(q+1)-a^(q+1)‖ = ‖(z^q-a^q)*a+z^q*(z-a)‖ := by congr 1; ring
      _ ≤ ‖z^q-a^q‖*‖a‖+‖z‖^q*‖z-a‖ := by
        simpa only [norm_mul,norm_pow] using norm_add_le ((z^q-a^q)*a) (z^q*(z-a))
      _ ≤ (((1+ε)^q-1)*‖a‖^q)*‖a‖+((1+ε)*‖a‖)^q*(ε*‖a‖) :=
        add_le_add (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
          (mul_le_mul hp hz (norm_nonneg _) (pow_nonneg (by positivity) _))
      _ = ((1+ε)^(q+1)-1)*‖a‖^(q+1) := by simp only [pow_succ,mul_pow]; ring

theorem moment_ball_error (s : Multiset ℂ) (q : ℕ) (a : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : ∀ z∈s, ‖z-a‖ ≤ ε*‖a‖) :
    ‖multisetPowerSum s q-(s.card:ℂ)*a^q‖ ≤
      (s.card:ℝ)*((1+ε)^q-1)*‖a‖^q := by
  classical
  have hpow : multisetPowerSum s q=∑ z : s,(z:ℂ)^q := by
    exact (congrArg Multiset.sum (Multiset.map_univ s (fun z : ℂ => z^q))).symm
  have he : multisetPowerSum s q-(s.card:ℂ)*a^q=∑ z : s,((z:ℂ)^q-a^q) := by
    rw [Finset.sum_sub_distrib]
    simp only [← hpow,Finset.sum_const,Finset.card_univ,Multiset.card_coe,nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ z : s,‖(z:ℂ)^q-a^q‖ := norm_sum_le _ _
    _ ≤ ∑ z : s,((1+ε)^q-1)*‖a‖^q := Finset.sum_le_sum fun z _ =>
      norm_power_perturbation q a (z:ℂ) ε hε (hs z Multiset.coe_mem)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Multiset.card_coe,nsmul_eq_mul,mul_assoc]

theorem zero_ball_moment_bound (s : Multiset ℂ) (q : ℕ) (a : ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hs : ∀ z∈s, ‖z‖ ≤ ρ*‖a‖) :
    ‖multisetPowerSum s q‖ ≤ (s.card:ℝ)*ρ^q*‖a‖^q := by
  classical
  have hpow : multisetPowerSum s q=∑ z : s,(z:ℂ)^q := by
    exact (congrArg Multiset.sum (Multiset.map_univ s (fun z : ℂ => z^q))).symm
  rw [hpow]
  calc
    _ ≤ ∑ z : s,‖(z:ℂ)^q‖ := norm_sum_le _ _
    _ ≤ ∑ z : s,(ρ*‖a‖)^q := Finset.sum_le_sum fun z _ => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hs z Multiset.coe_mem) q
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Multiset.card_coe,nsmul_eq_mul,mul_pow,mul_assoc]



end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open DerivativeChainPhaseLock











theorem solution (A B Z : Multiset ℂ) (q : ℕ) (hq : Odd q)
    (a : ℂ) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hA : ∀ z∈A, ‖z-a‖ ≤ ε*‖a‖)
    (hB : ∀ z∈B, ‖z+a‖ ≤ ε*‖a‖)
    (hZ : ∀ z∈Z, ‖z‖ ≤ ρ*‖a‖) :
    ‖_root_.DerivativeChainPhaseLock.multisetPowerSum (A+B+Z) q-(_root_.DerivativeChainPhaseLock.clusterImbalance A B:ℂ)*a^q‖ ≤
      _root_.DerivativeChainPhaseLock.clusterErrorBudget A B Z q ε ρ*‖a‖^q := by
  have heA := _root_.DerivativeChainPhaseLock.moment_ball_error A q a ε hε hA
  have heB := _root_.DerivativeChainPhaseLock.moment_ball_error B q (-a) ε hε (by simpa only [sub_neg_eq_add,norm_neg] using hB)
  have heZ := _root_.DerivativeChainPhaseLock.zero_ball_moment_bound Z q a ρ hρ hZ
  simp only [norm_neg,hq.neg_pow] at heB
  have he : _root_.DerivativeChainPhaseLock.multisetPowerSum (A+B+Z) q-(_root_.DerivativeChainPhaseLock.clusterImbalance A B:ℂ)*a^q =
      (_root_.DerivativeChainPhaseLock.multisetPowerSum A q-(A.card:ℂ)*a^q)+
      (_root_.DerivativeChainPhaseLock.multisetPowerSum B q-(B.card:ℂ)*(-a^q))+_root_.DerivativeChainPhaseLock.multisetPowerSum Z q := by
    simp only [_root_.DerivativeChainPhaseLock.multisetPowerSum,Multiset.map_add,Multiset.sum_add,_root_.DerivativeChainPhaseLock.clusterImbalance,
      Complex.ofReal_sub,Complex.ofReal_natCast]
    ring
  rw [he]
  have ht := (norm_add_le
    ((_root_.DerivativeChainPhaseLock.multisetPowerSum A q-(A.card:ℂ)*a^q)+(_root_.DerivativeChainPhaseLock.multisetPowerSum B q-(B.card:ℂ)*(-a^q)))
    (_root_.DerivativeChainPhaseLock.multisetPowerSum Z q)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  dsimp only [_root_.DerivativeChainPhaseLock.clusterErrorBudget]
  nlinarith only [ht,heA,heB,heZ]
