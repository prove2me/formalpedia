-- Prove2me | solution 1 for DerivativeChainClusterAnchor.dominant_cluster_eleven_thirds_array
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:39:02.167871+00:00
-- url     : https://prove2.me/submissions/5ba57541-4db4-4dcf-8c25-9766d7b4d4aa

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_actual_cluster_history_budget
import Theorems.Thm_DerivativeChainClusterAnchor_eleven_thirds_scalar_budget
import Theorems.Thm_DerivativeChainClusterAnchor_source_cluster_disk_moments
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DerivativeChainClusterAnchor

theorem cube_fraction_bound (N q k C : ℝ) (hN : 0 < N) (hq : 0 ≤ q) (hk : 0 < k)
    (hcube : C*q^3 ≤ N^2) (hscale : k^3 ≤ C*N) : k*q ≤ N := by
  by_contra h
  have hlt : N < k*q := lt_of_not_ge h
  have hx : 0 < k*q := hN.trans hlt
  have h1 := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hN)
  have h2 := mul_lt_mul_of_pos_right hlt (mul_pos hx hN)
  have h3 := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hx)
  have hu1 := mul_le_mul_of_nonneg_right hscale (pow_nonneg hq 3)
  have hu2 := mul_le_mul_of_nonneg_left hcube hN.le
  nlinarith





end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
namespace DerivativeChainClusterAnchor
noncomputable section





theorem cluster_outlier_cut (n r : ℕ) (hn : 16 ≤ n) (hr : 0 < r)
    (hcube : 4*r^3 ≤ n^2) : 2*r < n := by
  have hnR : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hc : (4:ℝ)*(r:ℝ)^3 ≤ (n:ℝ)^2 := by exact_mod_cast hcube
  have hbound := cube_fraction_bound (n:ℝ) (r:ℝ) 4 4 (by linarith) hrR.le (by norm_num) hc (by nlinarith)
  have ht : (2:ℝ)*(r:ℝ) < n := by linarith
  exact_mod_cast ht









end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor








theorem solution (n r : ℕ) (a : Fin (n+1) → ℂ)
    (o c : ℂ) (O : Finset (Fin (n+1))) (R ε : ℝ) (hn : 16 ≤ n+1) (hr : 0 < r)
    (hcube : 16*r^3 ≤ (n+1)^2) (hO : O.card ≤ r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hsmall : ε ≤ R/(16*(n+1:ℝ))) (hsource : ∀ i, ‖a i-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) :
    ∃ z : Fin (n+1) → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ (11/3:ℝ)*R ∧ (0 < R → _root_.DerivativeChainPrivate.chainCost z < 4*R) := by
  have hcut := _root_.DerivativeChainClusterAnchor.cluster_outlier_cut (n+1) r hn hr (by nlinarith [hcube])
  have hwide : ε ≤ R/(n+1:ℝ) := hsmall.trans
    (div_le_div_of_nonneg_left hR (by positivity)
      (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))
  have hm := _root_.DerivativeChainClusterAnchor.source_cluster_disk_moments n r a c o O hr hO R ε hR hε hwide hsource hc hnear
  let V := ∑ i, (n+1:ℝ)⁻¹*‖a i-_root_.DerivativeChainContinuation.complexCentroid a‖^2
  let δ := ‖_root_.DerivativeChainContinuation.complexCentroid a-c‖
  obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.actual_cluster_history_budget n r a c O hr hcut hO ε (2*R) hε hnear hm.1
  have hs := _root_.DerivativeChainClusterAnchor.eleven_thirds_scalar_budget (n+1) r hn hr hcube R V δ ε hR
    (by dsimp [V]; positivity) (norm_nonneg _) hε
    (by simpa only [V,Nat.cast_add,Nat.cast_one] using hm.2.1)
    (by simpa only [δ,Nat.cast_add,Nat.cast_one] using hm.2.2)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall)
  change _root_.DerivativeChainPrivate.chainCost z ≤ ((2*r-1:ℕ):ℝ)*Real.sqrt (V/(n:ℝ))+
    Real.sqrt (((2*r-1:ℕ):ℝ)*V/(n:ℝ)+δ^2)+4*(n+1:ℝ)*ε+
    16*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (2*R*ε/(n+1:ℝ)) at hcost
  have hcast : ((2*r-1:ℕ):ℝ)=2*(r:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*r)]
    push_cast
    rfl
  rw [hcast] at hcost
  norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hs
  have hfinal := hcost.trans hs
  exact ⟨z,hz,hfinal,fun hRpos => by nlinarith⟩
