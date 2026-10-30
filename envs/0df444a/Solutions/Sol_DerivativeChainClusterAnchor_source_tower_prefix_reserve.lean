-- Prove2me | solution 1 for DerivativeChainClusterAnchor.source_tower_prefix_reserve
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:51:16.951013+00:00
-- url     : https://prove2.me/submissions/368cd878-3430-4ed2-a2fb-6c74492525c7

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterPrefix
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_joint_complete_prefix_reserve
import Theorems.Thm_DerivativeChainPrefixLaws_scaled_sequence_contraction
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_variance_contraction
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
noncomputable section



theorem uniform_row_centroid (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    complexCentroid (r h)=r 0 0 := by
  induction h with
  | zero => simp [complexCentroid]
  | succ h ih =>
    rw [uniform_step_centroid r h (hstep h (by omega)),ih (by omega)]









theorem uniform_tower_variance_contraction (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) :
    (n:ℝ)*(∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-r 0 0‖^2) ≤
      (h:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖r n j-r 0 0‖^2) := by
  have hs (k : ℕ) (hk : k<n) :
      (k+1:ℝ)*secondMoment (fun j : Fin (k+1) => r k j-r 0 0) ≤
        (k:ℝ)*secondMoment (fun i : Fin (k+2) => r (k+1) i-r 0 0) :=
    uniform_step_variance_contraction r k (hstep k hk) (r 0 0)
      (uniform_row_centroid r n hstep (k+1) (by omega))
  have H := scaled_sequence_contraction
    (fun k => secondMoment (fun i : Fin (k+1) => r k i-r 0 0)) n h hh hs
  simpa only [secondMoment,Complex.normSq_eq_norm_sq,div_eq_mul_inv,
    Finset.mul_sum,Finset.sum_mul,mul_comm,Nat.cast_add,Nat.cast_one] using H

theorem uniform_tower_variance_contraction_div (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) :
    (∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-r 0 0‖^2) ≤
      (h:ℝ)/(n:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖r n j-r 0 0‖^2) := by
  by_cases hn : n=0
  · subst n
    have he : h=0 := by omega
    subst h
    simp
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnR).2
  simpa only [mul_comm] using uniform_tower_variance_contraction r n h hstep hh

end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor


theorem solution (r : _root_.DerivativeChainContinuation.ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, _root_.DerivativeChainContinuation.UniformPolynomialStep r k) (hh : h ≤ n) (c : ℂ) :
    ∃ z : Fin (h+1) → ℂ, _root_.DerivativeChainContinuation.IsComplexRowHistory r z ∧
      _root_.DerivativeChainPrivate.chainCost z+‖z (Fin.last h)-c‖ ≤
        (h:ℝ)*Real.sqrt (_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)/(n:ℝ))+
          Real.sqrt ((h:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)/(n:ℝ)+‖r 0 0-c‖^2) := by
  obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.joint_complete_prefix_reserve r h (fun k hk => hstep k (by omega)) c
  have hv : _root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0) ≤
      (h:ℝ)/(n:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0) := by
    simpa only [_root_.DerivativeChainClusterAnchor.rowCenteredVariance] using _root_.DerivativeChainPrefixLaws.uniform_tower_variance_contraction_div r n h hstep hh
  have hV : 0 ≤ _root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0) := by unfold _root_.DerivativeChainClusterAnchor.rowCenteredVariance; positivity
  have hscaled : (h:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0) ≤
      (h:ℝ)^2*(_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)/(n:ℝ)) := by
    have ht := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg h)
    exact ht.trans_eq (by ring)
  have hA : Real.sqrt ((h:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0)) ≤
      (h:ℝ)*Real.sqrt (_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)/(n:ℝ)) := by
    have ht := Real.sqrt_le_sqrt hscaled
    rw [Real.sqrt_mul (sq_nonneg (h:ℝ)),Real.sqrt_sq (Nat.cast_nonneg h)] at ht
    exact ht
  have hC : Real.sqrt (_root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0)+‖r 0 0-c‖^2) ≤
      Real.sqrt ((h:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)/(n:ℝ)+‖r 0 0-c‖^2) := by
    apply Real.sqrt_le_sqrt
    have he : (h:ℝ)/(n:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)=
        (h:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r n (r 0 0)/(n:ℝ) := by ring
    rw [he] at hv
    exact add_le_add hv le_rfl
  exact ⟨z,hz,hcost.trans (add_le_add hA hC)⟩
